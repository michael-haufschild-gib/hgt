import GaloisForLFunctions.RHTower.BaezDuarteWaveletNorm

/-!
# The causal Laplace transform of the beta wavelet

The substitution `y = e^{-2t}` turns the causal Laplace transform of `K_{k+1}` into a beta integral
on the unit interval with first parameter `(1+z)/2`, split by the sign factor into two beta values.
-/

namespace RHTower

open Real MeasureTheory

noncomputable section

/-- **Equation (14b).**  The causal Laplace transform of the beta wavelet, valid on the whole
half plane `Re z > -1` and in particular on the imaginary axis. -/
theorem laplace_bdKernel (k : ℕ) {z : ℂ} (hz : -1 < z.re) :
    (∫ t in Set.Ioi (0 : ℝ), ((bdKernel k t : ℝ) : ℂ) * Complex.exp (-(z * (t : ℂ))))
      = (1 / 2) * (Complex.betaIntegral ((1 + z) / 2) ((k : ℂ) + 1)
          - (2 * (k : ℂ) + 3) * Complex.betaIntegral ((1 + z) / 2 + 1) ((k : ℂ) + 1)) := by
  set a : ℂ := (1 + z) / 2 with ha
  have hare : 0 < a.re := by
    rw [ha]
    simp [Complex.add_re]
    nlinarith [hz, Complex.normSq_nonneg z]
  have hkre : 0 < (((k : ℂ) + 1)).re := by
    simp [Complex.add_re]
    positivity
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => Real.exp (-2 * t)) (-2 * Real.exp (-2 * t))
        (Set.Ioi (0 : ℝ)) t := by
    intro t _
    have hlin : HasDerivAt (fun t : ℝ => -2 * t) (-2 : ℝ) t := by
      simpa using (hasDerivAt_id' (x := t)).const_mul (-2 : ℝ)
    exact ((hlin.exp).congr_deriv (by ring)).hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => Real.exp (-2 * t)) (Set.Ioi 0) := by
    intro x _ y _ hxy
    have h := Real.exp_injective hxy
    linarith
  have hkey := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (measurableSet_Ioi) hderiv hinj
    (fun y : ℝ => (1 / 2 : ℂ) * ((y : ℂ) ^ (a - 1) * (1 - (y : ℂ)) ^ k
      * (1 - (2 * (k : ℂ) + 3) * (y : ℂ))))
  rw [image_exp_neg_two_mul] at hkey
  have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
      |(-2 : ℝ) * Real.exp (-2 * t)| • ((1 / 2 : ℂ)
          * (((Real.exp (-2 * t) : ℝ) : ℂ) ^ (a - 1)
            * (1 - ((Real.exp (-2 * t) : ℝ) : ℂ)) ^ k
            * (1 - (2 * (k : ℂ) + 3) * ((Real.exp (-2 * t) : ℝ) : ℂ))))
        = ((bdKernel k t : ℝ) : ℂ) * Complex.exp (-(z * (t : ℂ))) := by
    intro t _
    have hE : (0 : ℝ) < Real.exp (-2 * t) := Real.exp_pos _
    have habs : |(-2 : ℝ) * Real.exp (-2 * t)| = 2 * Real.exp (-2 * t) := by
      rw [abs_of_nonpos (by nlinarith)]
      ring
    have hne : ((Real.exp (-2 * t) : ℝ) : ℂ) ≠ 0 := by simp
    have hcpow : ((Real.exp (-2 * t) : ℝ) : ℂ) * ((Real.exp (-2 * t) : ℝ) : ℂ) ^ (a - 1)
        = ((Real.exp (-2 * t) : ℝ) : ℂ) ^ a := by
      calc ((Real.exp (-2 * t) : ℝ) : ℂ) * ((Real.exp (-2 * t) : ℝ) : ℂ) ^ (a - 1)
          = ((Real.exp (-2 * t) : ℝ) : ℂ) ^ (a - 1)
            * ((Real.exp (-2 * t) : ℝ) : ℂ) ^ (1 : ℂ) := by
            rw [Complex.cpow_one]; ring
        _ = ((Real.exp (-2 * t) : ℝ) : ℂ) ^ ((a - 1) + 1) := (Complex.cpow_add _ _ hne).symm
        _ = ((Real.exp (-2 * t) : ℝ) : ℂ) ^ a := by congr 1; ring
    have hval : ((Real.exp (-2 * t) : ℝ) : ℂ) ^ a
        = ((Real.exp (-t) : ℝ) : ℂ) * Complex.exp (-(z * (t : ℂ))) := by
      have hexpcpow : ((Real.exp (-2 * t) : ℝ) : ℂ) ^ a
          = Complex.exp (((-2 * t : ℝ) : ℂ) * a) := by
        rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos _).le,
          Real.log_exp]
      rw [hexpcpow, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      rw [ha]
      push_cast
      ring
    have hker : ((bdKernel k t : ℝ) : ℂ)
        = ((Real.exp (-t) : ℝ) : ℂ) * (1 - ((Real.exp (-2 * t) : ℝ) : ℂ)) ^ k
          * (1 - (2 * (k : ℂ) + 3) * ((Real.exp (-2 * t) : ℝ) : ℂ)) := by
      rw [bdKernel]
      push_cast
      ring
    have h2 : ((2 * Real.exp (-2 * t) : ℝ) : ℂ) = 2 * ((Real.exp (-2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [habs, hker, Complex.real_smul, h2]
    calc (2 : ℂ) * ((Real.exp (-2 * t) : ℝ) : ℂ)
          * ((1 / 2) * (((Real.exp (-2 * t) : ℝ) : ℂ) ^ (a - 1)
            * (1 - ((Real.exp (-2 * t) : ℝ) : ℂ)) ^ k
            * (1 - (2 * (k : ℂ) + 3) * ((Real.exp (-2 * t) : ℝ) : ℂ))))
        = (((Real.exp (-2 * t) : ℝ) : ℂ) * ((Real.exp (-2 * t) : ℝ) : ℂ) ^ (a - 1))
          * ((1 - ((Real.exp (-2 * t) : ℝ) : ℂ)) ^ k
            * (1 - (2 * (k : ℂ) + 3) * ((Real.exp (-2 * t) : ℝ) : ℂ))) := by ring
      _ = (((Real.exp (-t) : ℝ) : ℂ) * Complex.exp (-(z * (t : ℂ))))
          * ((1 - ((Real.exp (-2 * t) : ℝ) : ℂ)) ^ k
            * (1 - (2 * (k : ℂ) + 3) * ((Real.exp (-2 * t) : ℝ) : ℂ))) := by
            rw [hcpow, hval]
      _ = _ := by ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint] at hkey
  rw [← hkey]
  -- expand the unit-interval integral into two beta integrals
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  have hb1 := Complex.betaIntegral_convergent hare hkre
  have hb2 := Complex.betaIntegral_convergent (u := a + 1) (v := (k : ℂ) + 1)
    (by simpa [Complex.add_re] using by linarith [hare]) hkre
  have e1 : (∫ y in (0 : ℝ)..1, (1 / 2 : ℂ) * ((y : ℂ) ^ (a - 1) * (1 - (y : ℂ)) ^ k
        * (1 - (2 * (k : ℂ) + 3) * (y : ℂ))))
      = (1 / 2 : ℂ) * ∫ y in (0 : ℝ)..1, ((y : ℂ) ^ (a - 1) * (1 - (y : ℂ)) ^ k
        * (1 - (2 * (k : ℂ) + 3) * (y : ℂ))) :=
    intervalIntegral.integral_const_mul _ _
  have e2 : (∫ y in (0 : ℝ)..1, ((y : ℂ) ^ (a - 1) * (1 - (y : ℂ)) ^ k
        * (1 - (2 * (k : ℂ) + 3) * (y : ℂ))))
      = (∫ y in (0 : ℝ)..1, (y : ℂ) ^ (a - 1) * (1 - (y : ℂ)) ^ ((k : ℂ) + 1 - 1))
        - (2 * (k : ℂ) + 3)
          * ∫ y in (0 : ℝ)..1, (y : ℂ) ^ (a + 1 - 1) * (1 - (y : ℂ)) ^ ((k : ℂ) + 1 - 1) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hb1 (hb2.const_mul _)]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
    have h1 : ((k : ℂ) + 1 - 1) = ((k : ℕ) : ℂ) := by ring
    have h2 : (a + 1 - 1) = a := by ring
    rw [h1, h2, Complex.cpow_natCast]
    have h3 : (y : ℂ) ^ a = (y : ℂ) ^ (a - 1) * (y : ℂ) := by
      rcases eq_or_lt_of_le hy.1 with hy0 | hy0
      · have ha0 : a ≠ 0 := by
          intro hc
          rw [hc] at hare
          simp at hare
        rw [← hy0]
        rw [Complex.ofReal_zero, Complex.zero_cpow ha0]
        ring_nf
      · have hy0' : ((y : ℂ)) ≠ 0 := by
          simp only [ne_eq, Complex.ofReal_eq_zero]
          linarith
        rw [show (a : ℂ) = (a - 1) + 1 by ring, Complex.cpow_add _ _ hy0', Complex.cpow_one]
        ring_nf
    rw [h3]
    ring
  rw [e1, e2, Complex.betaIntegral, Complex.betaIntegral]


end

end RHTower
