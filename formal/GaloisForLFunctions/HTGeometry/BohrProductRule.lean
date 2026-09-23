import GaloisForLFunctions.HTGeometry.BohrMeanSquareBound

/-!
# The spectral product rule

If no pair of frequencies in the two spectra sums to `λ`, then `λ` is not a frequency of the
product.

Approximating each factor in mean square by its spectral partial sum, the product of the
approximants has no `λ`-mode at all, while the error in the `λ`-coefficient is controlled by the
mean-square errors through Cauchy–Schwarz.  Letting the approximation improve kills the coefficient.
-/

open MeasureTheory ComplexConjugate

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- **The spectral product rule.** -/
theorem bohrCoefficient_mul_eq_zero {f g : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htbf : HasTotallyBoundedOrbit (fun x => f x)) (hg : UniformContinuous (fun x => g x))
    (htbg : HasTotallyBoundedOrbit (fun x => g x)) {lam : ℝ}
    (hsep : ∀ mu nu : ℝ, mu + nu = lam →
      bohrCoefficient (fun x => f x) mu = 0 ∨ bohrCoefficient (fun x => g x) nu = 0) :
    bohrCoefficient (fun t => f t * g t) lam = 0 := by
  classical
  have hapf : IsBohrAlmostPeriodic (fun x => f x) :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htbf
  have hapg : IsBohrAlmostPeriodic (fun x => g x) :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htbg
  have hcf : Continuous (fun x => f x) := f.continuous
  have hcg : Continuous (fun x => g x) := g.continuous
  by_contra hne
  set d : ℝ := ‖bohrCoefficient (fun t => f t * g t) lam‖ with hd
  have hdpos : 0 < d := norm_pos_iff.mpr hne
  set N : ℝ := ‖f‖ + ‖g‖ + 1 with hN
  have hNpos : 0 < N := by
    have := norm_nonneg f
    have := norm_nonneg g
    positivity
  set r : ℝ := d / (2 * N) with hr
  have hrpos : 0 < r := by positivity
  set δ : ℝ := r ^ (2 : ℕ) with hδ'
  have hδ : 0 < δ := by positivity
  obtain ⟨S, hS⟩ := exists_spectral_mean_square_approx hf htbf hδ
  obtain ⟨T, hT⟩ := exists_spectral_mean_square_approx hg htbg hδ
  set p : ℝ → ℂ := trigPoly S (bohrCoefficient (fun x => f x)) with hp
  set q : ℝ → ℂ := trigPoly T (bohrCoefficient (fun x => g x)) with hq
  have hpc : Continuous p := continuous_trigPoly _ _
  have hpa : IsBohrAlmostPeriodic p := isBohrAlmostPeriodic_trigPoly _ _
  have hqc : Continuous q := continuous_trigPoly _ _
  have hqa : IsBohrAlmostPeriodic q := isBohrAlmostPeriodic_trigPoly _ _
  -- the product of the approximants has no `lam`-mode
  have hpq : bohrCoefficient (fun t => p t * q t) lam = 0 :=
    bohrCoefficient_trigPoly_mul_eq_zero S T _ _ lam fun mu _ nu _ hsum => by
      rcases hsep mu nu hsum with h | h
      · rw [h, zero_mul]
      · rw [h, mul_zero]
  -- splitting the difference
  have hsplit : bohrCoefficient (fun t => f t * g t) lam
      = bohrCoefficient (fun t => ((fun x => f x) t - p t) * (fun x => g x) t) lam
        + bohrCoefficient (fun t => p t * ((fun x => g x) t - q t)) lam := by
    have hc1 : Continuous fun t : ℝ => ((fun x => f x) t - p t) * (fun x => g x) t :=
      (hcf.sub hpc).mul hcg
    have ha1 : IsBohrAlmostPeriodic fun t : ℝ => ((fun x => f x) t - p t) * (fun x => g x) t :=
      isBohrAlmostPeriodic_mul (hcf.sub hpc) (isBohrAlmostPeriodic_sub hcf hapf hpc hpa) hcg hapg
    have hc2 : Continuous fun t : ℝ => p t * ((fun x => g x) t - q t) :=
      hpc.mul (hcg.sub hqc)
    have ha2 : IsBohrAlmostPeriodic fun t : ℝ => p t * ((fun x => g x) t - q t) :=
      isBohrAlmostPeriodic_mul hpc hpa (hcg.sub hqc)
        (isBohrAlmostPeriodic_sub hcg hapg hqc hqa)
    have hcpq : Continuous fun t : ℝ => p t * q t := hpc.mul hqc
    have hapq : IsBohrAlmostPeriodic fun t : ℝ => p t * q t :=
      isBohrAlmostPeriodic_mul hpc hpa hqc hqa
    have hfun : (fun t : ℝ => ((fun x => f x) t - p t) * (fun x => g x) t * bohrChar lam t
        + p t * ((fun x => g x) t - q t) * bohrChar lam t)
        = fun t : ℝ => ((fun x => f x) t * (fun x => g x) t) * bohrChar lam t
          - (p t * q t) * bohrChar lam t := by
      funext t
      ring
    have hsum := bohrMean_add
      (f := fun t : ℝ => ((fun x => f x) t - p t) * (fun x => g x) t * bohrChar lam t)
      (g := fun t : ℝ => p t * ((fun x => g x) t - q t) * bohrChar lam t)
      (hc1.mul (continuous_bohrChar lam)) (isBohrAlmostPeriodic_mul_bohrChar hc1 ha1 lam)
      (hc2.mul (continuous_bohrChar lam)) (isBohrAlmostPeriodic_mul_bohrChar hc2 ha2 lam)
    rw [hfun, bohrMean_sub
      (f := fun t : ℝ => ((fun x => f x) t * (fun x => g x) t) * bohrChar lam t)
      (g := fun t : ℝ => (p t * q t) * bohrChar lam t)
      ((hcf.mul hcg).mul (continuous_bohrChar lam))
      (isBohrAlmostPeriodic_mul_bohrChar (hcf.mul hcg)
        (isBohrAlmostPeriodic_mul hcf hapf hcg hapg) lam)
      (hcpq.mul (continuous_bohrChar lam))
      (isBohrAlmostPeriodic_mul_bohrChar hcpq hapq lam)] at hsum
    have hpq' : bohrMean (fun t : ℝ => (p t * q t) * bohrChar lam t) = 0 := hpq
    rw [hpq', sub_zero] at hsum
    exact hsum
  -- the two error coefficients are small
  have hbound1 : ‖bohrCoefficient (fun t => ((fun x => f x) t - p t) * (fun x => g x) t) lam‖ ^ (2 : ℕ)
      ≤ δ * ‖g‖ ^ (2 : ℕ) := by
    refine le_trans (norm_bohrCoefficient_mul_sq_le (hcf.sub hpc)
      (isBohrAlmostPeriodic_sub hcf hapf hpc hpa) hcg hapg lam) ?_
    exact mul_le_mul hS (bohrMean_mul_conj_re_le_norm_sq hapg)
      (bohrMean_mul_conj_re_nonneg hcg hapg) hδ.le
  have hbound2 : ‖bohrCoefficient (fun t => p t * ((fun x => g x) t - q t)) lam‖ ^ (2 : ℕ)
      ≤ ‖f‖ ^ (2 : ℕ) * δ := by
    refine le_trans (norm_bohrCoefficient_mul_sq_le hpc hpa (hcg.sub hqc)
      (isBohrAlmostPeriodic_sub hcg hapg hqc hqa) lam) ?_
    refine mul_le_mul ?_ hT (bohrMean_mul_conj_re_nonneg (hcg.sub hqc)
      (isBohrAlmostPeriodic_sub hcg hapg hqc hqa)) (by positivity)
    exact le_trans (bohrMean_trigPoly_mul_conj_self_re_le hapf S)
      (bohrMean_mul_conj_re_le_norm_sq hapf)
  -- contradiction
  have hdle : d ≤ ‖bohrCoefficient (fun t => ((fun x => f x) t - p t) * (fun x => g x) t) lam‖
      + ‖bohrCoefficient (fun t => p t * ((fun x => g x) t - q t)) lam‖ := by
    rw [hd, hsplit]
    exact norm_add_le _ _
  set x : ℝ := ‖bohrCoefficient (fun t => ((fun x => f x) t - p t) * (fun x => g x) t) lam‖
    with hxdef
  set y : ℝ := ‖bohrCoefficient (fun t => p t * ((fun x => g x) t - q t)) lam‖ with hydef
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hfn : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hgn : (0 : ℝ) ≤ ‖g‖ := norm_nonneg g
  have hx1 : x ≤ r * ‖g‖ := by
    have h := Real.sqrt_le_sqrt hbound1
    rw [Real.sqrt_sq hx] at h
    have hsq : Real.sqrt (δ * ‖g‖ ^ (2 : ℕ)) = r * ‖g‖ := by
      rw [hδ', ← mul_pow, Real.sqrt_sq (by positivity)]
    rwa [hsq] at h
  have hy1 : y ≤ ‖f‖ * r := by
    have h := Real.sqrt_le_sqrt hbound2
    rw [Real.sqrt_sq hy] at h
    have hsq : Real.sqrt (‖f‖ ^ (2 : ℕ) * δ) = ‖f‖ * r := by
      rw [hδ', ← mul_pow, Real.sqrt_sq (by positivity)]
    rwa [hsq] at h
  have hrN : r * (‖f‖ + ‖g‖) < d := by
    rw [hr, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hdpos, hfn, hgn]
  have hfinal : d ≤ r * ‖g‖ + ‖f‖ * r := le_trans hdle (add_le_add hx1 hy1)
  nlinarith [hrN, hfinal]

end

end GaloisForLFunctions
