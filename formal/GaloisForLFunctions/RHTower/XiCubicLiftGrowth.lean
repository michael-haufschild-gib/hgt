import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing
import GaloisForLFunctions.HTGeometry.OrderOneEnvelopeRootDivision

/-!
# Growth of a hypothetical actual Xi cubic lift

For `(f-3)f²=4 ξ(s) exp(-as)`, a root bound transfers the actual order-one
envelope to f. Xi's superlinear logarithmic growth transfers along the real ray.
Finite-zero subquadratic rigidity therefore forces infinitely many zeros of f.
The lift equation is retained here; the companion strip argument excludes it.
-/

namespace GaloisForLFunctions.HTGeometry
open Complex

/-- A direct root bound for the normalized cubic, including its double branch. -/
theorem norm_le_of_cubic_factor (x d : ℂ) (h : (x - 3) * x ^ 2 = 4 * d) :
    ‖x‖ ≤ 6 + 8 * ‖d‖ := by
  have hx := norm_nonneg x
  have hd := norm_nonneg d
  by_cases h6 : ‖x‖ < 6
  · linarith
  · have hn : ‖x - 3‖ * ‖x‖ ^ 2 = 4 * ‖d‖ := by
      simpa only [norm_mul, norm_pow, norm_ofNat] using congrArg norm h
    have hsub : ‖x‖ - 3 ≤ ‖x - 3‖ := by
      simpa using norm_sub_norm_le x (3 : ℂ)
    have hmul := mul_le_mul_of_nonneg_right hsub (sq_nonneg ‖x‖)
    have hc : ‖x‖ ^ 3 ≤ 8 * ‖d‖ := by nlinarith [sq_nonneg (‖x‖ - 6)]
    nlinarith [sq_nonneg (‖x‖ - 1)]

/-- Polynomial lifting preserves the source's order-one envelope. -/
theorem OrderOneEnvelope.of_cubic_factor {f d : ℂ → ℂ} (hd : OrderOneEnvelope d)
    (hrel : ∀ z, (f z - 3) * f z ^ 2 = 4 * d z) : OrderOneEnvelope f := by
  have hnorm : OrderOneEnvelope (fun z => (‖d z‖ : ℂ)) := by
    obtain ⟨C, hC, hb⟩ := hd
    refine ⟨C, hC, fun z => ?_⟩
    simpa using hb z
  obtain ⟨C, hC, hb⟩ := (orderOneEnvelope_const (6 : ℂ)).add (hnorm.const_mul 8)
  refine ⟨C, hC, fun z => ?_⟩
  have heq : ‖(6 : ℂ) + 8 * (‖d z‖ : ℂ)‖ = 6 + 8 * ‖d z‖ := by
    have hcast : (6 : ℂ) + 8 * (‖d z‖ : ℂ) = ((6 + 8 * ‖d z‖ : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (norm_le_of_cubic_factor _ _ (hrel z)).trans (heq ▸ hb z)

end GaloisForLFunctions.HTGeometry

namespace RHTower
open Complex GaloisForLFunctions.HTGeometry

/-- Every hypothetical cubic lift has a factor of superlinear logarithmic ray growth. -/
theorem cubic_xi_factor_superlinear_ray (a : ℝ) {f : ℂ → ℂ}
    (hrel : ∀ z, (f z - 3) * f z ^ 2 = 4 * (xi z * Complex.exp (-(a : ℂ) * z)))
    (A : ℝ) : ∃ σ : ℝ, 1 ≤ σ ∧ A * σ < Real.log ‖f (σ : ℂ)‖ := by
  let B := max 1 A
  obtain ⟨σ, hσ, hbig⟩ := riemannXi_ray_growth (3 * B + a)
  refine ⟨σ, hσ, ?_⟩
  have hB : 1 ≤ B := le_max_left _ _
  have hAB : A ≤ B := le_max_right _ _
  have hE : 1 ≤ Real.exp (B * σ) := Real.one_le_exp (by positivity)
  have hfnz : f (σ : ℂ) ≠ 0 := by
    intro hfzero
    have h := hrel (σ : ℂ)
    simp only [hfzero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
    have hxi := xi_ne_zero_of_ofReal σ
    exact (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0)
      (mul_ne_zero hxi (Complex.exp_ne_zero _))) h.symm
  by_contra hnot
  have hflog : Real.log ‖f (σ : ℂ)‖ ≤ B * σ :=
    (le_of_not_gt hnot).trans (mul_le_mul_of_nonneg_right hAB (by linarith))
  have hfbound : ‖f (σ : ℂ)‖ ≤ Real.exp (B * σ) := by
    rw [← Real.exp_log (norm_pos_iff.mpr hfnz)]
    exact Real.exp_le_exp.mpr hflog
  have hsub : ‖f (σ : ℂ) - 3‖ ≤ 4 * Real.exp (B * σ) := by
    have h := norm_sub_le (f (σ : ℂ)) (3 : ℂ)
    norm_num at h
    linarith
  have hnorm := congrArg norm (hrel (σ : ℂ))
  have hexp : ‖Complex.exp (-(a : ℂ) * (σ : ℂ))‖ = Real.exp (-a * σ) := by
    simp [Complex.norm_exp]
  simp only [norm_mul, norm_pow, norm_ofNat, hexp] at hnorm
  have hprod : ‖f (σ : ℂ) - 3‖ * ‖f (σ : ℂ)‖ ^ 2 ≤
      4 * Real.exp (3 * B * σ) := by
    calc
      _ ≤ (4 * Real.exp (B * σ)) * (Real.exp (B * σ)) ^ 2 :=
        mul_le_mul hsub (pow_le_pow_left₀ (norm_nonneg _) hfbound 2) (sq_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; congr 2; ring
  have hxi : ‖xi (σ : ℂ)‖ ≤ Real.exp ((3 * B + a) * σ) := by
    have htemp : ‖xi (σ : ℂ)‖ * Real.exp (-a * σ) ≤ Real.exp (3 * B * σ) := by
      nlinarith [hprod, hnorm]
    calc
      ‖xi (σ : ℂ)‖ = (‖xi (σ : ℂ)‖ * Real.exp (-a * σ)) * Real.exp (a * σ) := by
        rw [mul_assoc, ← Real.exp_add, show -a * σ + a * σ = 0 by ring,
          Real.exp_zero, mul_one]
      _ ≤ Real.exp (3 * B * σ) * Real.exp (a * σ) :=
        mul_le_mul_of_nonneg_right htemp (Real.exp_pos (a * σ)).le
      _ = Real.exp ((3 * B + a) * σ) := by rw [← Real.exp_add]; congr 1; ring
  rw [← xi_eq_riemannXi] at hbig
  have hlog := Real.log_le_log (norm_pos_iff.mpr (xi_ne_zero_of_ofReal σ)) hxi
  rw [Real.log_exp] at hlog
  exact (not_lt_of_ge hlog) hbig

/-- Finite-order rigidity forces infinitely many zeros of the hypothetical double-branch factor. -/
theorem xi_cubic_factor_zeroSet_infinite (a : ℝ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hrel : ∀ z, (f z - 3) * f z ^ 2 = 4 * (xi z * Complex.exp (-(a : ℂ) * z))) :
    {z : ℂ | f z = 0}.Infinite := by
  have hxi : OrderOneEnvelope xi := orderOneEnvelope_riemannXi.congr
    (fun z => (xi_eq_riemannXi z).symm)
  have hd := hxi.mul (orderOneEnvelope_exp_mul (-(a : ℂ)))
  obtain ⟨C, hC, hgrow⟩ := (hd.of_cubic_factor hrel).subquadratic
  exact zeroSet_infinite_of_subquadratic_superlinear_ray hf
    (by norm_num) (by norm_num) hC hgrow (cubic_xi_factor_superlinear_ray a hrel)

end RHTower
