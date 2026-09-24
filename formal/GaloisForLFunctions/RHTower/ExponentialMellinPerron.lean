import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversionGeneralLine

/-!
# Exponentially smoothed Perron inversion for an arbitrary Dirichlet series

The Cahen--Mellin integral `(1/2π)∫ y^{-(c+it)} Γ(c+it) dt = e^{-y}` inverts termwise, and the
resulting double integral is absolutely convergent as soon as the Dirichlet series converges
absolutely on the line.  Hence for every coefficient sequence with `∑ ‖a n‖ n^{-c} < ∞`,

```text
∑_{n ≥ 1} a n e^{-n x} = (1/2π) ∫_ℝ x^{-(c+it)} Γ(c+it) L(a, c+it) dt.
```

No boundedness of the coefficients is assumed; the exponential weight makes the vertical integral
absolutely convergent whatever the polynomial growth of the Dirichlet series, which is what lets a
later contour shift cross the critical strip.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- The `n`-th piece of the exponentially smoothed Mellin integrand. -/
def expMellinTerm (a : ℕ → ℂ) (c x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  a n * ((((n : ℝ) * x : ℝ) : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) *
    Complex.Gamma ((c : ℂ) + (t : ℂ) * I))

theorem norm_expMellinTerm {a : ℕ → ℂ} {c x : ℝ} (hx : 0 < x) (ha0 : a 0 = 0)
    (n : ℕ) (t : ℝ) :
    ‖expMellinTerm a c x n t‖
      = ‖a n‖ * ((n : ℝ) * x) ^ (-c) * ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [expMellinTerm, ha0]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnx : (0 : ℝ) < (n : ℝ) * x := by nlinarith
    rw [expMellinTerm, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hnx]
    have hre : (-((c : ℂ) + (t : ℂ) * I)).re = -c := by simp
    rw [hre, mul_assoc]

theorem integrable_expMellinTerm {a : ℕ → ℂ} {c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (ha0 : a 0 = 0) (n : ℕ) : Integrable (expMellinTerm a c x n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : expMellinTerm a c x 0 = fun _ : ℝ => (0 : ℂ) := by
      funext t; simp [expMellinTerm, ha0]
    rw [hz]
    exact integrable_zero _ _ _
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnx : (0 : ℝ) < (n : ℝ) * x := by nlinarith
  have hne : ((((n : ℝ) * x : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnx.ne'
  have hΓ : Integrable (fun t : ℝ => Complex.Gamma ((c : ℂ) + (t : ℂ) * I)) :=
    GaloisForLFunctions.SelbergClass.gamma_verticalIntegrable_of_pos hc
  have hmaj : Integrable (fun t : ℝ =>
      ‖a n‖ * ((n : ℝ) * x) ^ (-c) * ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖) :=
    hΓ.norm.const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    refine continuous_const.mul (Continuous.mul ?_ ?_)
    · exact Continuous.const_cpow (by fun_prop) (Or.inl hne)
    · exact GaloisForLFunctions.SelbergClass.continuous_Gamma_line_of_pos hc
  · exact Filter.Eventually.of_forall fun t => le_of_eq (norm_expMellinTerm hx ha0 n t)

theorem integral_norm_expMellinTerm {a : ℕ → ℂ} {c x : ℝ} (_hc : 0 < c) (hx : 0 < x)
    (ha0 : a 0 = 0) (n : ℕ) :
    (∫ t : ℝ, ‖expMellinTerm a c x n t‖)
      = (‖a n‖ * (n : ℝ) ^ (-c))
          * (x ^ (-c) * ∫ t : ℝ, ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖) := by
  have hsplit : ((n : ℝ) * x) ^ (-c) = (n : ℝ) ^ (-c) * x ^ (-c) :=
    Real.mul_rpow (Nat.cast_nonneg n) hx.le
  have hcongr : (fun t : ℝ => ‖expMellinTerm a c x n t‖)
      = fun t : ℝ => (‖a n‖ * ((n : ℝ) ^ (-c) * x ^ (-c)))
          * ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ := by
    funext t
    rw [norm_expMellinTerm hx ha0 n t, hsplit, mul_assoc]
  rw [hcongr, MeasureTheory.integral_const_mul]
  ring

theorem summable_integral_norm_expMellinTerm {a : ℕ → ℂ} {c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (ha0 : a 0 = 0) (hsum : Summable (fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-c))) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖expMellinTerm a c x n t‖) := by
  have h := hsum.mul_right (x ^ (-c) * ∫ t : ℝ, ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖)
  refine h.congr (fun n => ?_)
  exact (integral_norm_expMellinTerm hc hx ha0 n).symm

theorem integral_expMellinTerm {a : ℕ → ℂ} {c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (ha0 : a 0 = 0) (n : ℕ) :
    (∫ t : ℝ, expMellinTerm a c x n t)
      = ((2 * Real.pi : ℝ) : ℂ) * (a n * Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : expMellinTerm a c x 0 = fun _ : ℝ => (0 : ℂ) := by
      funext t; simp [expMellinTerm, ha0]
    rw [hz, ha0]
    simp
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnx : (0 : ℝ) < (n : ℝ) * x := by nlinarith
  have hCM := GaloisForLFunctions.SelbergClass.mellinInv_line_Gamma_eq_exp_neg hc hnx
  rw [mellinInv] at hCM
  have hpull : (∫ t : ℝ, expMellinTerm a c x n t)
      = a n * ∫ t : ℝ, ((((n : ℝ) * x : ℝ) : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) *
          Complex.Gamma ((c : ℂ) + (t : ℂ) * I)) := by
    rw [← MeasureTheory.integral_const_mul]
    rfl
  have hsmul : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, ((((n : ℝ) * x : ℝ) : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) *
        Complex.Gamma ((c : ℂ) + (t : ℂ) * I)))
      = Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) := by
    rw [← hCM]
    simp [Complex.real_smul, smul_eq_mul]
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hinv : (∫ t : ℝ, ((((n : ℝ) * x : ℝ) : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) *
      Complex.Gamma ((c : ℂ) + (t : ℂ) * I)))
      = ((2 * Real.pi : ℝ) : ℂ) * Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) := by
    have h1 : ((1 / (2 * Real.pi) : ℝ) : ℂ) = (((2 * Real.pi : ℝ) : ℂ))⁻¹ := by
      push_cast; ring
    rw [h1] at hsmul
    field_simp at hsmul
    linear_combination hsmul
  rw [hpull, hinv]
  ring

theorem tsum_expMellinTerm {a : ℕ → ℂ} {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (ha0 : a 0 = 0)
    (t : ℝ) :
    (∑' n : ℕ, expMellinTerm a c x n t)
      = (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) *
        (Complex.Gamma ((c : ℂ) + (t : ℂ) * I) * LSeries a ((c : ℂ) + (t : ℂ) * I)) := by
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
  have hs0 : s ≠ 0 := by
    intro hcon
    have hre := congrArg Complex.re hcon
    rw [hs] at hre
    simp at hre
    linarith
  have hsplit : ∀ n : ℕ, expMellinTerm a c x n t
      = ((x : ℂ) ^ (-s) * Complex.Gamma s) * (a n * (n : ℂ) ^ (-s)) := by
    intro n
    have hcp : ((((n : ℝ) * x : ℝ)) : ℂ) ^ (-s) = ((n : ℝ) : ℂ) ^ (-s) * ((x : ℝ) : ℂ) ^ (-s) := by
      have := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (α := ℝ) n) hx.le (-s)
      push_cast at this ⊢
      exact this
    rw [expMellinTerm, ← hs, hcp]
    push_cast
    ring
  have hterm : ∀ n : ℕ, a n * (n : ℂ) ^ (-s) = LSeries.term a s n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, ha0]
    · rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), Complex.cpow_neg, div_eq_mul_inv]
  calc (∑' n : ℕ, expMellinTerm a c x n t)
      = ∑' n : ℕ, ((x : ℂ) ^ (-s) * Complex.Gamma s) * LSeries.term a s n := by
        refine tsum_congr (fun n => ?_)
        rw [hsplit n, hterm n]
    _ = ((x : ℂ) ^ (-s) * Complex.Gamma s) * LSeries a s := by
        rw [tsum_mul_left]; rfl
    _ = (x : ℂ) ^ (-s) * (Complex.Gamma s * LSeries a s) := by ring

/-- **Exponentially smoothed Perron inversion.** -/
theorem mellinInv_gamma_mul_LSeries_eq_tsum_exp {a : ℕ → ℂ} {c : ℝ} (hc : 0 < c) (ha0 : a 0 = 0)
    (hsum : Summable (fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-c))) {x : ℝ} (hx : 0 < x) :
    mellinInv c (fun s => Complex.Gamma s * LSeries a s) x
      = ∑' n : ℕ, a n * Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) := by
  have hHS := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (F := expMellinTerm a c x) (fun n => integrable_expMellinTerm hc hx ha0 n)
    (summable_integral_norm_expMellinTerm hc hx ha0 hsum)
  have hleft : (fun n : ℕ => ∫ t : ℝ, expMellinTerm a c x n t)
      = fun n : ℕ => ((2 * Real.pi : ℝ) : ℂ) * (a n * Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ))) := by
    funext n
    exact integral_expMellinTerm hc hx ha0 n
  rw [hleft] at hHS
  have hsumval := hHS.tsum_eq
  rw [tsum_mul_left] at hsumval
  have hright : (∫ t : ℝ, ∑' n : ℕ, expMellinTerm a c x n t)
      = ∫ t : ℝ, (x : ℂ) ^ (-((c : ℂ) + (t : ℂ) * I)) *
          (Complex.Gamma ((c : ℂ) + (t : ℂ) * I) * LSeries a ((c : ℂ) + (t : ℂ) * I)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    exact tsum_expMellinTerm hc hx ha0 t
  rw [hright] at hsumval
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  rw [mellinInv]
  have hsm : (∫ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + (y : ℂ) * I)) •
      (Complex.Gamma ((c : ℂ) + (y : ℂ) * I) * LSeries a ((c : ℂ) + (y : ℂ) * I)))
      = ((2 * Real.pi : ℝ) : ℂ) * ∑' n : ℕ, a n * Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) := by
    simp only [smul_eq_mul]
    exact hsumval.symm
  rw [hsm]
  rw [Complex.real_smul]
  push_cast
  field_simp
  exact tsum_congr fun n => by rw [mul_comm (x : ℂ) (n : ℂ)]

end

end RHTower
