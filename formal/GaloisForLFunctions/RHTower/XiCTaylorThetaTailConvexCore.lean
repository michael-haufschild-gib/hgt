import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreIntegral

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

theorem thetaCuspTailEvenCoefficient_eq_second_integral (n : ℕ) :
    thetaCuspTailEvenCoefficient n =
      2 * ∫ x : ℝ in Ioi 0,
        x ^ (2 * n + 2) * thetaCuspTailDerivative 2 x /
          (2 * n + 2).factorial := by
  have h := integral_pow_mul_thetaCuspTailDerivative_two
    (k := 2 * n + 2) (by omega)
  have hsub1 : 2 * n + 2 - 1 = 2 * n + 1 := by omega
  have hsub2 : 2 * n + 2 - 2 = 2 * n := by omega
  rw [hsub1, hsub2] at h
  rw [thetaCuspTailEvenCoefficient, thetaCuspTailRawEvenMoment]
  rw [show (fun x : ℝ =>
      x ^ (2 * n + 2) * thetaCuspTailDerivative 2 x /
        (2 * n + 2).factorial) =
      fun x : ℝ => (x ^ (2 * n + 2) * thetaCuspTailDerivative 2 x) *
        ((2 * n + 2).factorial : ℝ)⁻¹ by
    funext x
    rw [div_eq_mul_inv]]
  rw [MeasureTheory.integral_mul_const, h]
  have hfac : (2 * n + 2).factorial =
      (2 * n).factorial * (2 * n + 1) * (2 * n + 2) := by
    calc
      (2 * n + 2).factorial = (2 * n + 1).factorial * (2 * n + 2) := by
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ]
        ring
      _ = ((2 * n).factorial * (2 * n + 1)) * (2 * n + 2) := by
        rw [Nat.factorial_succ]
        ring
  rw [hfac]
  push_cast
  field_simp

theorem thetaCuspTailDerivativePolynomial_two :
    thetaCuspTailDerivativePolynomial 2 =
      C (1 / 4) - C (6 * Real.pi) * X ^ 2 +
        C (4 * Real.pi ^ 2) * X ^ 4 := by
  apply Polynomial.funext
  intro u
  simp [thetaCuspTailDerivativePolynomial, thetaCuspLogDerivativeStep]
  ring

theorem thetaCuspTailDerivativePolynomial_two_eval_pos
    {u : ℝ} (hu : 1 ≤ u) :
    0 < eval u (thetaCuspTailDerivativePolynomial 2) := by
  rw [thetaCuspTailDerivativePolynomial_two]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hv : 3 < Real.pi * u ^ 2 := by
    have huSq : 1 ≤ u ^ 2 := by nlinarith
    nlinarith [Real.pi_pos]
  have hv0 : 0 < Real.pi * u ^ 2 := lt_trans (by norm_num) hv
  nlinarith [sq_nonneg (Real.pi * u ^ 2)]

theorem thetaCuspTailDerivative_two_atom_pos
    {q : ℕ} (hq : 0 < q) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspPolynomialAtom (thetaCuspTailDerivativePolynomial 2) q x := by
  rw [thetaCuspPolynomialAtom]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hexp1 : 1 ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr hx
  have hy : 1 ≤ (q : ℝ) * Real.exp x := by nlinarith [Real.exp_pos x]
  have heval := thetaCuspTailDerivativePolynomial_two_eval_pos hy
  positivity

theorem thetaCuspTailDerivative_two_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspTailDerivative 2 x := by
  rw [thetaCuspTailDerivative]
  have hs := summable_thetaCuspTailDerivative 2 x
  exact hs.tsum_pos
    (fun n => (thetaCuspTailDerivative_two_atom_pos (Nat.succ_pos n) hx).le)
    0 (thetaCuspTailDerivative_two_atom_pos (by omega) hx)

theorem integral_Ioi_thetaCuspTailDerivative_two :
    (∫ x : ℝ in Ioi 0, thetaCuspTailDerivative 2 x) = 1 / 4 := by
  have h := integral_Ioi_thetaCuspFullSource_mul_cos 0
  norm_num at h
  rw [show (fun x : ℝ => thetaCuspFullSource x) =
      fun x => thetaCuspTailDerivative 2 x -
        (1 / 4 : ℝ) * thetaCuspTailDerivative 0 x by
      funext x
      rw [thetaCuspFullSource_eq_tail_second_sub]] at h
  rw [integral_sub (integrableOn_thetaCuspTailDerivative_Ioi 2)
      ((integrableOn_thetaCuspTailDerivative_Ioi 0).const_mul (1 / 4 : ℝ)),
    integral_const_mul] at h
  linarith

def thetaCuspTailSecondDensity (x : ℝ) : ℝ :=
  4 * thetaCuspTailDerivative 2 x

theorem thetaCuspTailSecondDensity_pos {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspTailSecondDensity x := by
  unfold thetaCuspTailSecondDensity
  positivity [thetaCuspTailDerivative_two_pos hx.le]

theorem integral_thetaCuspTailSecondDensity :
    (∫ x : ℝ in Ioi 0, thetaCuspTailSecondDensity x) = 1 := by
  unfold thetaCuspTailSecondDensity
  rw [MeasureTheory.integral_const_mul,
    integral_Ioi_thetaCuspTailDerivative_two]
  norm_num

theorem thetaCuspTailEvenCoefficient_eq_second_complex_integral (n : ℕ) :
    (thetaCuspTailEvenCoefficient n : ℂ) =
      (1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          ((x : ℂ) ^ (2 * n + 2) / (2 * n + 2).factorial) := by
  rw [thetaCuspTailEvenCoefficient_eq_second_integral]
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        ((x : ℂ) ^ (2 * n + 2) / (2 * n + 2).factorial)) =
      fun x : ℝ => ((4 *
        (x ^ (2 * n + 2) * thetaCuspTailDerivative 2 x /
          (2 * n + 2).factorial) : ℝ) : ℂ) by
    funext x
    unfold thetaCuspTailSecondDensity
    push_cast
    ring]
  have hcast :
      (∫ x : ℝ in Ioi 0, ((4 *
        (x ^ (2 * n + 2) * thetaCuspTailDerivative 2 x /
          (2 * n + 2).factorial) : ℝ) : ℂ)) =
      (((∫ x : ℝ in Ioi 0, 4 *
        (x ^ (2 * n + 2) * thetaCuspTailDerivative 2 x /
          (2 * n + 2).factorial)) : ℝ) : ℂ) := by
    exact integral_ofReal (X := ℝ) (μ := volume.restrict (Ioi 0)) (𝕜 := ℂ)
  rw [hcast]
  rw [MeasureTheory.integral_const_mul]
  push_cast
  ring

def thetaCuspTailSecondSection (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℂ) ^ k * z ^ (2 * k) *
      ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)

theorem integrableOn_thetaCuspTailSecondDensity_complex :
    IntegrableOn (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ))
      (Ioi 0) := by
  have hbase : IntegrableOn
      (fun x : ℝ => (thetaCuspTailDerivative 2 x : ℂ)) (Ioi 0) :=
    (integrableOn_thetaCuspTailDerivative_Ioi 2).ofReal
  rw [show (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ)) =
      fun x : ℝ => (4 : ℂ) * (thetaCuspTailDerivative 2 x : ℂ) by
    funext x
    unfold thetaCuspTailSecondDensity
    push_cast
    ring]
  exact hbase.const_mul (4 : ℂ)

theorem integral_thetaCuspTailSecondDensity_complex :
    (∫ x : ℝ in Ioi 0, (thetaCuspTailSecondDensity x : ℂ)) = 1 := by
  have hcast :
      (∫ x : ℝ in Ioi 0, (thetaCuspTailSecondDensity x : ℂ)) =
        (((∫ x : ℝ in Ioi 0, thetaCuspTailSecondDensity x) : ℝ) : ℂ) := by
    exact integral_ofReal (X := ℝ) (μ := volume.restrict (Ioi 0)) (𝕜 := ℂ)
  rw [hcast, integral_thetaCuspTailSecondDensity]
  norm_num

theorem integrableOn_thetaCuspTailSecondDensity_mul_term
    (k : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        ((-1 : ℂ) ^ k * z ^ (2 * k) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial))) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun x : ℝ => ((x ^ (2 * k + 2) *
        thetaCuspTailDerivative 2 x : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_pow_mul_thetaCuspTailDerivative (2 * k + 2) 2).ofReal
  let c : ℂ := 4 * ((-1 : ℂ) ^ k * z ^ (2 * k)) *
    (((2 * k + 2).factorial : ℂ)⁻¹)
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        ((-1 : ℂ) ^ k * z ^ (2 * k) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial))) =
      fun x : ℝ => c *
        ((x ^ (2 * k + 2) * thetaCuspTailDerivative 2 x : ℝ) : ℂ) by
    funext x
    unfold thetaCuspTailSecondDensity
    dsimp [c]
    push_cast
    rw [div_eq_mul_inv]
    ring]
  exact hbase.const_mul c

theorem integrableOn_thetaCuspTailSecondDensity_mul_section
    (d : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondSection d z x) (Ioi 0) := by
  unfold thetaCuspTailSecondSection
  rw [show (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * z ^ (2 * k) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (thetaCuspTailSecondDensity x : ℂ) *
          ((-1 : ℂ) ^ k * z ^ (2 * k) *
            ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) by
    funext x
    rw [Finset.mul_sum]]
  exact MeasureTheory.integrable_finset_sum _ fun k _ =>
    integrableOn_thetaCuspTailSecondDensity_mul_term k z

theorem thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_second_integral
    (d : ℕ) (z : ℂ) :
    (thetaCuspTailEvenPolynomial d).eval₂ (algebraMap ℝ ℂ) (-z ^ 2) =
      (1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondSection d z x := by
  rw [thetaCuspTailEvenPolynomial]
  unfold thetaCuspTailSecondSection
  rw [show (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
      ∑ k ∈ Finset.range (d + 1),
        (-1 : ℂ) ^ k * z ^ (2 * k) *
          ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) =
      fun x : ℝ => ∑ k ∈ Finset.range (d + 1),
        (thetaCuspTailSecondDensity x : ℂ) *
          ((-1 : ℂ) ^ k * z ^ (2 * k) *
            ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) by
    funext x
    rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finset_sum]
  · rw [show eval₂ (algebraMap ℝ ℂ) (-z ^ 2)
        (∑ k ∈ Finset.range (d + 1),
          C (thetaCuspTailEvenCoefficient k) * X ^ k) =
        ∑ k ∈ Finset.range (d + 1),
          eval₂ (algebraMap ℝ ℂ) (-z ^ 2)
            (C (thetaCuspTailEvenCoefficient k) * X ^ k) by
      change (Polynomial.eval₂RingHom (algebraMap ℝ ℂ) (-z ^ 2))
          (∑ k ∈ Finset.range (d + 1),
            C (thetaCuspTailEvenCoefficient k) * X ^ k) = _
      rw [map_sum]
      simp only [Polynomial.coe_eval₂RingHom]]
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (thetaCuspTailEvenCoefficient k : ℂ) * (-z ^ 2) ^ k = _
    rw [thetaCuspTailEvenCoefficient_eq_second_complex_integral]
    calc
      ((1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) *
            ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) *
            (-z ^ 2) ^ k =
          (1 / 2 : ℂ) * ((∫ x : ℝ in Ioi 0,
            (thetaCuspTailSecondDensity x : ℂ) *
              ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) *
                (-z ^ 2) ^ k) := by ring
      _ = (1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
          ((thetaCuspTailSecondDensity x : ℂ) *
            ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) *
              (-z ^ 2) ^ k := by
        rw [MeasureTheory.integral_mul_const]
      _ = (1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) *
            ((-1 : ℂ) ^ k * z ^ (2 * k) *
              ((x : ℂ) ^ (2 * k + 2) / (2 * k + 2).factorial)) := by
        congr 2
        funext x
        rw [neg_pow, ← pow_mul]
        ring
  · intro k _
    have hbase : IntegrableOn
        (fun x : ℝ => ((x ^ (2 * k + 2) *
          thetaCuspTailDerivative 2 x : ℝ) : ℂ)) (Ioi 0) :=
      (integrableOn_pow_mul_thetaCuspTailDerivative (2 * k + 2) 2).ofReal
    let c : ℂ := 4 * ((-1 : ℂ) ^ k * z ^ (2 * k)) *
      (((2 * k + 2).factorial : ℂ)⁻¹)
    have hscaled := hbase.const_mul c
    convert hscaled using 1
    funext x
    unfold thetaCuspTailSecondDensity
    dsimp [c]
    push_cast
    rw [div_eq_mul_inv]
    ring

def thetaCuspTailSecondCoreAtom (d : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  1 - (z ^ 2 + 1 / 4) * thetaCuspTailSecondSection d z x

theorem xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral
    (d : ℕ) (z : ℂ) :
    (xiCTaylorThetaTailCorePolynomial d).eval z =
      (1 / 2 : ℂ) * ∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x := by
  rw [xiCTaylorThetaTailCorePolynomial, evenMagnitudeLift_eval]
  simp only [eval₂_add, eval₂_C, eval₂_mul, eval₂_sub, eval₂_X]
  rw [thetaCuspTailEvenPolynomial_eval₂_neg_sq_eq_second_integral]
  have hmass := integrableOn_thetaCuspTailSecondDensity_complex
  have hsection :=
    integrableOn_thetaCuspTailSecondDensity_mul_section d z
  have hcore :
      (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x) =
      1 - (z ^ 2 + 1 / 4) *
        ∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) *
            thetaCuspTailSecondSection d z x := by
    unfold thetaCuspTailSecondCoreAtom
    rw [show (fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) *
        (1 - (z ^ 2 + 1 / 4) * thetaCuspTailSecondSection d z x)) =
        fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) -
          (z ^ 2 + 1 / 4) *
            ((thetaCuspTailSecondDensity x : ℂ) *
              thetaCuspTailSecondSection d z x) by
      funext x
      ring]
    rw [integral_sub hmass (hsection.const_mul (z ^ 2 + 1 / 4)),
      integral_const_mul, integral_thetaCuspTailSecondDensity_complex]
  rw [hcore]
  push_cast
  ring

theorem thetaCuspTailSecondSection_zero (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondSection 0 z x = (x : ℂ) ^ 2 / 2 := by
  simp [thetaCuspTailSecondSection]

/-- Probability positivity does not orient the convex-core atoms pointwise: at degree zero an
explicit atom has strictly positive upper-half-plane current. -/
theorem exists_thetaCuspTailSecondCoreAtom_zero_current_pos :
    ∃ x y : ℝ, 0 < y ∧
      0 < ((-((x : ℂ) ^ 2) * ((y : ℂ) * I)) *
        (starRingEnd ℂ)
          (thetaCuspTailSecondCoreAtom 0 ((y : ℂ) * I) x)).im := by
  refine ⟨4, 1 / 4, by norm_num, ?_⟩
  rw [show thetaCuspTailSecondCoreAtom 0
      ((((1 / 4 : ℝ) : ℂ)) * I) 4 = -(1 / 2 : ℂ) by
    rw [thetaCuspTailSecondCoreAtom, thetaCuspTailSecondSection_zero]
    rw [show ((4 : ℝ) : ℂ) ^ 2 = (16 : ℂ) by norm_num]
    rw [show ((((1 / 4 : ℝ) : ℂ)) * I) ^ 2 = (-1 / 16 : ℂ) by
      rw [mul_pow, Complex.I_sq]
      push_cast
      ring]
    norm_num]
  rw [show (starRingEnd ℂ) (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) by
    rw [map_neg, map_div₀, map_one, map_ofNat]]
  rw [show ((4 : ℝ) : ℂ) ^ 2 = (16 : ℂ) by norm_num]
  norm_num

end
end RHTower
