import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay

/-!
# Sharp decay of `Γ` on an arbitrary vertical strip off the real axis

The corpus bounds `‖Γ(σ+it)‖` by `C|t|^N e^{-π|t|/2}` uniformly on a vertical strip with positive
abscissas.  The functional equation `Γ(z+1) = zΓ(z)` transports the bound to an arbitrary strip:
off the real axis every factor `z+j` has modulus at least one, so shifting the abscissa to the right
can only increase the modulus of `Γ`.

## Main results

* `norm_Gamma_le_norm_Gamma_add_nat`
* `exists_sharp_bound_norm_Gamma_strip`
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- Off the real axis, shifting the abscissa right can only increase `‖Γ‖`. -/
theorem norm_Gamma_le_norm_Gamma_add_nat {z : ℂ} (hz : 1 ≤ |z.im|) (k : ℕ) :
    ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + (k : ℂ))‖ := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hne : z + (n : ℂ) ≠ 0 := by
      intro h
      have him : (z + (n : ℂ)).im = 0 := by rw [h]; simp
      rw [Complex.add_im, Complex.natCast_im, add_zero] at him
      rw [him] at hz
      norm_num at hz
    have hcast : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
    have hstep : Complex.Gamma (z + ((n + 1 : ℕ) : ℂ))
        = (z + (n : ℂ)) * Complex.Gamma (z + (n : ℂ)) := by
      rw [hcast, show z + ((n : ℂ) + 1) = (z + (n : ℂ)) + 1 from by ring,
        Complex.Gamma_add_one _ hne]
    rw [hstep, norm_mul]
    have hge : (1 : ℝ) ≤ ‖z + (n : ℂ)‖ := by
      refine le_trans hz ?_
      have him : (z + (n : ℂ)).im = z.im := by
        rw [Complex.add_im, Complex.natCast_im, add_zero]
      calc |z.im| = |(z + (n : ℂ)).im| := by rw [him]
        _ ≤ ‖z + (n : ℂ)‖ := Complex.abs_im_le_norm _
    nlinarith [norm_nonneg (Complex.Gamma (z + (n : ℂ))), ih]

/-- **Sharp decay of `Γ` on an arbitrary vertical strip, off the real axis.** -/
theorem exists_sharp_bound_norm_Gamma_strip (α β : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ z : ℂ, α ≤ z.re → z.re ≤ β → 1 ≤ |z.im| →
      ‖Complex.Gamma z‖ ≤ C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 2)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < α + (k : ℝ) := by
    refine ⟨⌈|α|⌉₊ + 1, ?_⟩
    have h1 : |α| ≤ (⌈|α|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : -α ≤ |α| := neg_le_abs α
    push_cast
    linarith
  obtain ⟨C, N, hC, hb⟩ := exists_bound_norm_Gamma_vertical_strip hk (β + (k : ℝ))
  refine ⟨C, N, hC, fun z h1 h2 h3 => ?_⟩
  have hle := norm_Gamma_le_norm_Gamma_add_nat h3 k
  have hz : z + (k : ℂ) = ((z.re + (k : ℝ) : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
    refine Complex.ext ?_ ?_ <;> simp
  rw [hz] at hle
  exact le_trans hle (hb (z.re + (k : ℝ)) z.im (by linarith) (by linarith) h3)

/-- The sine is bounded by the exponential of the height. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have hsin : Complex.sin z = (Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I))
      * Complex.I / 2 := rfl
  have h1 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [hsin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have hle : ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖
      ≤ Real.exp z.im + Real.exp (-z.im) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [h1, h2]
  have hcosh : Real.exp z.im + Real.exp (-z.im) ≤ 2 * Real.exp |z.im| := by
    have hup : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
    have hdown : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
    linarith
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  linarith

/-- **Sharp growth of `1/Γ` on an arbitrary vertical strip, off the real axis.** -/
theorem exists_bound_norm_inv_Gamma_strip (α β : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ z : ℂ, α ≤ z.re → z.re ≤ β → 1 ≤ |z.im| →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * |z.im| ^ N * Real.exp (Real.pi * |z.im| / 2) := by
  obtain ⟨C, N, hC, hb⟩ := exists_sharp_bound_norm_Gamma_strip (1 - β) (1 - α)
  refine ⟨C / Real.pi, N, by positivity, fun z h1 h2 h3 => ?_⟩
  have hzim : z.im ≠ 0 := by
    intro h
    rw [h] at h3
    norm_num at h3
  have hGne : Complex.Gamma z ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m => ?_)
    intro hm
    refine hzim ?_
    have him : z.im = (-(m : ℂ)).im := by rw [hm]
    simpa using him
  have hG1ne : Complex.Gamma (1 - z) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m => ?_)
    intro hm
    refine hzim ?_
    have him : (1 - z).im = (-(m : ℂ)).im := by rw [hm]
    rw [Complex.sub_im, Complex.one_im, zero_sub] at him
    simpa using him
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hsne : Complex.sin (((Real.pi : ℝ) : ℂ) * z) ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at hrefl
    rcases mul_eq_zero.1 hrefl with h | h
    · exact hGne h
    · exact hG1ne h
  have hkey : Complex.Gamma z * Complex.Gamma (1 - z) * Complex.sin (((Real.pi : ℝ) : ℂ) * z)
      = ((Real.pi : ℝ) : ℂ) := (eq_div_iff hsne).1 hrefl
  have hnorms : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖
      * ‖Complex.sin (((Real.pi : ℝ) : ℂ) * z)‖ = Real.pi := by
    have h := congrArg norm hkey
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h
    exact h
  have hGpos : 0 < ‖Complex.Gamma z‖ := norm_pos_iff.2 hGne
  have hinvval : ‖Complex.Gamma z‖⁻¹
      = ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (((Real.pi : ℝ) : ℂ) * z)‖ / Real.pi := by
    have hcalc : ‖Complex.Gamma z‖⁻¹ * Real.pi
        = ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (((Real.pi : ℝ) : ℂ) * z)‖ := by
      calc ‖Complex.Gamma z‖⁻¹ * Real.pi
          = ‖Complex.Gamma z‖⁻¹ * (‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖
              * ‖Complex.sin (((Real.pi : ℝ) : ℂ) * z)‖) := by rw [hnorms]
        _ = (‖Complex.Gamma z‖⁻¹ * ‖Complex.Gamma z‖)
            * (‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (((Real.pi : ℝ) : ℂ) * z)‖) := by ring
        _ = ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (((Real.pi : ℝ) : ℂ) * z)‖ := by
            rw [inv_mul_cancel₀ (ne_of_gt hGpos), one_mul]
    rw [eq_div_iff (ne_of_gt Real.pi_pos)]
    exact hcalc
  have hre1 : 1 - β ≤ (1 - z).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hre2 : (1 - z).re ≤ 1 - α := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have him1 : |(1 - z).im| = |z.im| := by
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  have hG := hb (1 - z) hre1 hre2 (by rw [him1]; exact h3)
  rw [him1] at hG
  have himpi : |(((Real.pi : ℝ) : ℂ) * z).im| = Real.pi * |z.im| := by
    rw [Complex.mul_im]
    simp [abs_mul, abs_of_pos Real.pi_pos]
  have hsin := norm_sin_le_exp_abs_im (((Real.pi : ℝ) : ℂ) * z)
  rw [himpi] at hsin
  have hexp : Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (Real.pi * |z.im|)
      = Real.exp (Real.pi * |z.im| / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfinal : ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (((Real.pi : ℝ) : ℂ) * z)‖
      ≤ C * |z.im| ^ N * Real.exp (Real.pi * |z.im| / 2) := by
    calc ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (((Real.pi : ℝ) : ℂ) * z)‖
        ≤ (C * |z.im| ^ N * Real.exp (-(Real.pi * |z.im| / 2))) * Real.exp (Real.pi * |z.im|) :=
          mul_le_mul hG hsin (norm_nonneg _) (by positivity)
      _ = C * |z.im| ^ N * (Real.exp (-(Real.pi * |z.im| / 2)) * Real.exp (Real.pi * |z.im|)) := by
          ring
      _ = C * |z.im| ^ N * Real.exp (Real.pi * |z.im| / 2) := by rw [hexp]
  rw [norm_inv, hinvval]
  have hsplit : C / Real.pi * |z.im| ^ N * Real.exp (Real.pi * |z.im| / 2)
      = (C * |z.im| ^ N * Real.exp (Real.pi * |z.im| / 2)) / Real.pi := by
    field_simp
  rw [hsplit]
  gcongr


end

end GaloisForLFunctions.HTGeometry
