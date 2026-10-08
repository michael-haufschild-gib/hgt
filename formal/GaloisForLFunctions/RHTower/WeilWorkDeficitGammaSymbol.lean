import GaloisForLFunctions.RHTower.WeilWorkDeficitGammaDensity

/-!
# Exact reciprocal-Gamma symbol on the inversion line

The actual entire Xi-square quotient satisfies a polynomial-clearing identity
at every complex argument, including apparent Gamma poles. Reflection and
duplication identify its full value on `re s = 2`, where the clearing product
never vanishes. This pays the algebraic symbol in WP06 C23; Mellin inversion,
the asymptotic and the spectral-deficit bound remain separate obligations.
-/

noncomputable section
open Complex
open scoped BigOperators
namespace RHTower.WeilWorkDeficitGamma

/-- Product of the apparent poles introduced by integer Gamma shifts. -/
def clearingProduct (N : ℕ) (s : ℂ) : ℂ :=
  ∏ j ∈ Finset.range N, (s+2*(j:ℂ)+2)*(s-(2*(j:ℂ)+3))

/-- Reciprocal recurrence preserves the actual entire value even at Gamma poles. -/
theorem spectralMellin_step (N : ℕ) (s : ℂ) :
    (s+2*(N:ℂ)+2)*(s-(2*(N:ℂ)+3))*spectralMellin (N+2) s =
      -4*spectralMellin (N+1) s := by
  have h1 := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
    (((N:ℂ)+1)+s/2)
  have h2 := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
    (((N:ℂ)+1)+1/2-s/2)
  have ha : (N:ℂ)+1+s/2+1 = (N:ℂ)+2+s/2 := by ring
  have hb : (N:ℂ)+1+1/2-s/2+1 = (N:ℂ)+2+1/2-s/2 := by ring
  simp only [spectralMellin, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    div_eq_mul_inv, mul_inv_rev]
  simp only [div_eq_mul_inv] at h1 h2 ha hb
  rw [h1, h2, ha, hb]
  ring

/-- Global pole-clearing formula, with no excluded complex arguments. -/
theorem clearingProduct_spectralMellin (N : ℕ) (s : ℂ) :
    clearingProduct N s*spectralMellin (N+1) s =
      (-4:ℂ)^N*spectralMellin 1 s := by
  induction N with
  | zero => simp [clearingProduct]
  | succ N ih =>
    rw [clearingProduct, Finset.prod_range_succ]
    change (clearingProduct N s * ((s+2*(N:ℂ)+2)*(s-(2*(N:ℂ)+3)))) *
      spectralMellin (N+2) s = _
    rw [mul_assoc, spectralMellin_step]
    calc
      clearingProduct N s*(-4*spectralMellin (N+1) s) =
          -4*(clearingProduct N s*spectralMellin (N+1) s) := by ring
      _ = _ := by rw [ih, pow_succ]; ring

private theorem clearingProduct_two_ne_zero (N : ℕ) (t : ℝ) :
    clearingProduct N (2+(t:ℂ)*I) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply mul_ne_zero
  · apply Complex.ne_zero_of_re_pos
    simp
    positivity
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    linarith

private theorem spectralMellin_one_two (t : ℝ) :
    spectralMellin 1 (2+(t:ℂ)*I) =
      -2/(Real.sqrt Real.pi:ℂ) * (2+(t:ℂ)*I) * (1+(t:ℂ)*I) *
        (2*(Real.pi:ℂ))^(-(2+(t:ℂ)*I)) * Complex.Gamma (2+(t:ℂ)*I) *
        Complex.cos ((Real.pi:ℂ)*(2+(t:ℂ)*I)/2) *
        riemannZeta (2+(t:ℂ)*I)^2 := by
  let s : ℂ := 2+(t:ℂ)*I
  have hs : s.re = 2 := by simp [s]
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (by rw [hs]; norm_num)
  have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.re h; rw [hs] at this; norm_num at this
  have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr : (Real.sqrt Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hr2 : (Real.sqrt Real.pi:ℂ)^2 = (Real.pi:ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hg0 : Complex.Gamma (s/2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num [hs])
  have hga : Complex.Gamma ((s-1)/2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num [hs])
  have hgb : Complex.Gamma (1-(s-1)/2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num [hs])
  have hsin : Complex.sin ((Real.pi:ℂ)*((s-1)/2)) =
      -Complex.cos ((Real.pi:ℂ)*s/2) := by
    rw [show (Real.pi:ℂ)*((s-1)/2) = (Real.pi:ℂ)*s/2-(Real.pi:ℂ)/2 by ring,
      Complex.sin_sub, Complex.sin_pi_div_two, Complex.cos_pi_div_two]
    ring
  have href := Complex.Gamma_mul_Gamma_one_sub ((s-1)/2)
  rw [hsin] at href
  have hcos : Complex.cos ((Real.pi:ℂ)*s/2) ≠ 0 := by
    intro h
    rw [h, neg_zero, div_zero] at href
    exact mul_ne_zero hga hgb href
  have hinv : (Complex.Gamma (1-(s-1)/2))⁻¹ =
      -Complex.Gamma ((s-1)/2)*Complex.cos ((Real.pi:ℂ)*s/2)/(Real.pi:ℂ) := by
    have hprod := (eq_div_iff (neg_ne_zero.mpr hcos)).mp href
    generalize Complex.Gamma ((s-1)/2) = A at *
    generalize Complex.Gamma (1-(s-1)/2) = B at *
    generalize Complex.cos ((Real.pi:ℂ)*s/2) = C at *
    field_simp [hgb, hπ]
    linear_combination -hprod
  have hdup := Complex.Gamma_mul_Gamma_add_half ((s-1)/2)
  rw [show (s-1)/2+1/2 = s/2 by ring,
    show 2*((s-1)/2) = s-1 by ring,
    show 1-(s-1) = (2:ℂ)-s by ring] at hdup
  have hpow : (2:ℂ)^(2-s) = 4*(2:ℂ)^(-s) := by
    rw [show (2:ℂ)-s = 1+1+(-s) by ring,
      Complex.cpow_add _ _ (by norm_num),
      Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
    ring
  rw [hpow] at hdup
  have hgam : Complex.Gamma s = (s-1)*Complex.Gamma (s-1) := by
    rw [← Complex.Gamma_add_one _ (sub_ne_zero.mpr hs1)]
    congr 1
    ring
  have hgam1 : Complex.Gamma (1+s/2) = s/2*Complex.Gamma (s/2) := by
    rw [add_comm, Complex.Gamma_add_one _ (div_ne_zero hs0 (by norm_num))]
  have hpisq : ((Real.pi:ℂ)^(-s/2))^2 = (Real.pi:ℂ)^(-s) := by
    rw [pow_two, ← Complex.cpow_add _ _ hπ]
    congr 1
    ring
  have hpimul : (2*(Real.pi:ℂ))^(-s) = (2:ℂ)^(-s)*(Real.pi:ℂ)^(-s) :=
    Complex.mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le (-s)
  have hxi := xi_eq_archFactor_mul_zeta hs0 hs1
    (Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num))
  change spectralMellin 1 s = -2/(Real.sqrt Real.pi:ℂ)*s*(1+(t:ℂ)*I)*
    (2*(Real.pi:ℂ))^(-s)*Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*riemannZeta s^2
  rw [show (1:ℂ)+(t:ℂ)*I = s-1 by dsimp [s]; ring]
  unfold spectralMellin
  rw [hxi, archFactor, Complex.Gammaℝ_def]
  norm_num only [Nat.cast_one]
  rw [show (3:ℂ)/2-s/2 = 1-(s-1)/2 by ring, hgam1]
  simp only [mul_pow, div_pow]
  rw [hpisq, div_eq_mul_inv, mul_inv_rev, hinv, hpimul, hgam]
  field_simp [hg0, hs0, hπ, hr]
  linear_combination -riemannZeta s^2 * Complex.cos (s*(Real.pi:ℂ)/2) *
    (Real.sqrt Real.pi:ℂ) * hdup -
    4*riemannZeta s^2*Complex.cos (s*(Real.pi:ℂ)/2)*Complex.Gamma (s-1)*(2:ℂ)^(-s)*hr2

/-- The actual weighted Xi-square has the exact divisor-cosine symbol on the inversion line. -/
theorem spectralMellin_two (N : ℕ) (t : ℝ) :
    spectralMellin (N+1) (2+(t:ℂ)*I) =
      (-4:ℂ)^N * (-2/(Real.sqrt Real.pi:ℂ)) *
        ((2+(t:ℂ)*I)*(1+(t:ℂ)*I) / clearingProduct N (2+(t:ℂ)*I)) *
        (2*(Real.pi:ℂ))^(-(2+(t:ℂ)*I)) * Complex.Gamma (2+(t:ℂ)*I) *
        Complex.cos ((Real.pi:ℂ)*(2+(t:ℂ)*I)/2) *
        riemannZeta (2+(t:ℂ)*I)^2 := by
  have h := clearingProduct_spectralMellin N (2+(t:ℂ)*I)
  rw [spectralMellin_one_two] at h
  apply (mul_left_cancel₀ (clearingProduct_two_ne_zero N t))
  rw [h]
  field_simp [clearingProduct_two_ne_zero N t]

end RHTower.WeilWorkDeficitGamma
