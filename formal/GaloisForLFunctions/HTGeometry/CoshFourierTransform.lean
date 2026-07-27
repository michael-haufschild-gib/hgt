import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# The Fourier transform of a hyperbolic power

The logistic substitution `v = e^t/(2 cosh t)` carries the whole line onto the unit interval and
turns the oscillatory hyperbolic power integral into a complex Euler Beta integral:

```text
∫_ℝ (cosh t)^(-s) e^(-i x t) dt = 2^(s-1) Γ((s-ix)/2) Γ((s+ix)/2) / Γ(s) .
```

The two logarithmic identities behind it are `log v = t - log (2 cosh t)` and
`log (1-v) = -t - log (2 cosh t)`, so the Beta integrand `v^(a-1)(1-v)^(b-1)` with
`a = (s-ix)/2`, `b = (s+ix)/2` is `e^(-ixt) (2 cosh t)^(2-s)`, and the Jacobian
`dv = dt/(2 cosh² t)` produces the factor `2^(1-s)`.
-/

open MeasureTheory Set

namespace HTGeometry

noncomputable section

/-! ### The logistic substitution -/

/-- The logistic substitution variable `v = e^t/(2 cosh t)`. -/
def logisticVar (t : ℝ) : ℝ := Real.exp t / (2 * Real.cosh t)

theorem logisticVar_pos (t : ℝ) : 0 < logisticVar t := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  exact div_pos (Real.exp_pos t) (by linarith)

theorem one_sub_logisticVar (t : ℝ) :
    1 - logisticVar t = Real.exp (-t) / (2 * Real.cosh t) := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have hne : (2 * Real.cosh t) ≠ 0 := by linarith
  rw [logisticVar, Real.cosh_eq]
  field_simp
  ring

theorem one_sub_logisticVar_pos (t : ℝ) : 0 < 1 - logisticVar t := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  rw [one_sub_logisticVar]
  exact div_pos (Real.exp_pos _) (by linarith)

theorem logisticVar_lt_one (t : ℝ) : logisticVar t < 1 := by
  have := one_sub_logisticVar_pos t
  linarith

theorem hasDerivAt_logisticVar (t : ℝ) :
    HasDerivAt logisticVar (1 / (2 * Real.cosh t ^ 2)) t := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have hne : (2 * Real.cosh t) ≠ 0 := by linarith
  have hden : HasDerivAt (fun u : ℝ => 2 * Real.cosh u) (2 * Real.sinh t) t := by
    simpa using (Real.hasDerivAt_cosh t).const_mul 2
  have h := (Real.hasDerivAt_exp t).div hden hne
  have hcs : Real.cosh t - Real.sinh t = Real.exp (-t) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hval : (Real.exp t * (2 * Real.cosh t) - Real.exp t * (2 * Real.sinh t)) /
      (2 * Real.cosh t) ^ 2 = 1 / (2 * Real.cosh t ^ 2) := by
    rw [show Real.exp t * (2 * Real.cosh t) - Real.exp t * (2 * Real.sinh t)
        = 2 * (Real.exp t * (Real.cosh t - Real.sinh t)) by ring, hcs, hexp]
    field_simp
  rw [hval] at h
  exact h

theorem logisticVar_strictMono : StrictMono logisticVar := by
  refine strictMono_of_deriv_pos fun t => ?_
  rw [(hasDerivAt_logisticVar t).deriv]
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  positivity

theorem logisticVar_eq_exp (t : ℝ) :
    logisticVar t = Real.exp (2 * t) / (Real.exp (2 * t) + 1) := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have hE : (0 : ℝ) < Real.exp (2 * t) := Real.exp_pos _
  have hexp : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp' : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [logisticVar, Real.cosh_eq, hexp]
  have hpos : Real.exp t > 0 := Real.exp_pos t
  field_simp
  nlinarith [hexp', hpos]

theorem logisticVar_image_univ : logisticVar '' Set.univ = Set.Ioo 0 1 := by
  ext v
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨logisticVar_pos t, logisticVar_lt_one t⟩
  · intro hv
    have h0 : (0 : ℝ) < v := hv.1
    have h1 : v < 1 := hv.2
    have hq : (0 : ℝ) < v / (1 - v) := div_pos h0 (by linarith)
    refine ⟨(1 / 2) * Real.log (v / (1 - v)), Set.mem_univ _, ?_⟩
    have hE : Real.exp (2 * ((1 / 2) * Real.log (v / (1 - v)))) = v / (1 - v) := by
      rw [show (2 : ℝ) * ((1 / 2) * Real.log (v / (1 - v))) = Real.log (v / (1 - v)) by ring,
        Real.exp_log hq]
    rw [logisticVar_eq_exp, hE]
    have h1v : (1 : ℝ) - v ≠ 0 := by linarith
    field_simp
    ring

/-! ### The two logarithmic identities -/

theorem log_logisticVar (t : ℝ) :
    Real.log (logisticVar t) = t - Real.log (2 * Real.cosh t) := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  rw [logisticVar, Real.log_div (Real.exp_pos t).ne' (by linarith), Real.log_exp]

theorem log_one_sub_logisticVar (t : ℝ) :
    Real.log (1 - logisticVar t) = -t - Real.log (2 * Real.cosh t) := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  rw [one_sub_logisticVar, Real.log_div (Real.exp_pos _).ne' (by linarith), Real.log_exp]

/-! ### The complex power of a positive real -/

theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ((r : ℝ) : ℂ) ^ z = Complex.exp ((Real.log r : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne')]
  congr 1
  rw [Complex.ofReal_log hr.le]

/-! ### The Beta integrand in hyperbolic coordinates -/

/-- The Beta integrand transported by the logistic substitution. -/
theorem betaIntegrand_logisticVar {s x : ℝ} (t : ℝ) :
    ((logisticVar t : ℝ) : ℂ) ^ ((((s : ℂ) - (x : ℂ) * Complex.I) / 2) - 1) *
        ((1 : ℂ) - ((logisticVar t : ℝ) : ℂ)) ^ ((((s : ℂ) + (x : ℂ) * Complex.I) / 2) - 1)
      = Complex.exp (-((x : ℂ) * (t : ℂ)) * Complex.I) *
        ((2 * Real.cosh t : ℝ) : ℂ) ^ ((2 : ℂ) - (s : ℂ)) := by
  have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
  have h2c : (0 : ℝ) < 2 * Real.cosh t := by linarith
  have hv : (0 : ℝ) < logisticVar t := logisticVar_pos t
  have hv' : (0 : ℝ) < 1 - logisticVar t := one_sub_logisticVar_pos t
  have hcast : (1 : ℂ) - ((logisticVar t : ℝ) : ℂ) = ((1 - logisticVar t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, ofReal_cpow_eq_exp hv, ofReal_cpow_eq_exp hv', ofReal_cpow_eq_exp h2c,
    ← Complex.exp_add, log_logisticVar, log_one_sub_logisticVar]
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

/-! ### The Fourier transform -/

theorem betaIntegral_eq_setIntegral (a b : ℂ) :
    Complex.betaIntegral a b
      = ∫ v in Set.Ioo (0 : ℝ) 1, ((v : ℝ) : ℂ) ^ (a - 1) * ((1 : ℂ) - ((v : ℝ) : ℂ)) ^ (b - 1) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **The Fourier transform of a hyperbolic power.** -/
theorem integral_cosh_rpow_neg_mul_exp {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (∫ t : ℝ, (((Real.cosh t) ^ (-s) : ℝ) : ℂ) *
        Complex.exp (-((x : ℂ) * (t : ℂ)) * Complex.I))
      = ((2 : ℝ) ^ (s - 1) : ℝ) *
        (Complex.Gamma (((s : ℂ) - (x : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((s : ℂ) + (x : ℂ) * Complex.I) / 2) / Complex.Gamma (s : ℂ)) := by
  have hinj : Set.InjOn logisticVar Set.univ :=
    Set.injOn_of_injective logisticVar_strictMono.injective
  have hderiv : ∀ t ∈ Set.univ,
      HasDerivWithinAt logisticVar (1 / (2 * Real.cosh t ^ 2)) Set.univ t :=
    fun t _ => (hasDerivAt_logisticVar t).hasDerivWithinAt
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ hderiv hinj
    (fun v : ℝ => ((v : ℝ) : ℂ) ^ ((((s : ℂ) - (x : ℂ) * Complex.I) / 2) - 1) *
      ((1 : ℂ) - ((v : ℝ) : ℂ)) ^ ((((s : ℂ) + (x : ℂ) * Complex.I) / 2) - 1))
  rw [logisticVar_image_univ] at hchange
  have hpt : ∀ t : ℝ, |1 / (2 * Real.cosh t ^ 2)| •
      (((logisticVar t : ℝ) : ℂ) ^ ((((s : ℂ) - (x : ℂ) * Complex.I) / 2) - 1) *
        ((1 : ℂ) - ((logisticVar t : ℝ) : ℂ)) ^ ((((s : ℂ) + (x : ℂ) * Complex.I) / 2) - 1))
      = (((2 : ℝ) ^ (1 - s) : ℝ) : ℂ) * ((((Real.cosh t) ^ (-s) : ℝ) : ℂ) *
        Complex.exp (-((x : ℂ) * (t : ℂ)) * Complex.I)) := by
    intro t
    have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
    have h2c : (0 : ℝ) < 2 * Real.cosh t := by linarith
    rw [betaIntegrand_logisticVar t, abs_of_pos (by positivity), Complex.real_smul]
    have hsplit : ((2 * Real.cosh t : ℝ) : ℂ) ^ ((2 : ℂ) - (s : ℂ))
        = (((2 : ℝ) ^ (2 - s) : ℝ) : ℂ) * (((Real.cosh t ^ (2 - s) : ℝ)) : ℂ) := by
      rw [show ((2 : ℂ) - (s : ℂ)) = (((2 - s : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow h2c.le, Real.mul_rpow (by norm_num) hc.le]
      push_cast
      ring
    rw [hsplit]
    have hcosh : ((Real.cosh t ^ (2 - s) : ℝ) : ℂ)
        = (((Real.cosh t) ^ (-s) : ℝ) : ℂ) * (((Real.cosh t ^ (2 : ℝ) : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hc]
      congr 2
      ring
    have hsq : (Real.cosh t ^ (2 : ℝ) : ℝ) = Real.cosh t ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have htwo : ((2 : ℝ) ^ (2 - s) : ℝ) = ((2 : ℝ) ^ (1 - s) : ℝ) * 2 := by
      rw [show (2 : ℝ) - s = (1 - s) + 1 by ring, Real.rpow_add (by norm_num)]
      norm_num
    rw [hcosh, hsq, htwo]
    have hcne : ((Real.cosh t : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact hc.ne'
    have hcne' : Complex.cosh (t : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_cosh]
      exact hcne
    push_cast
    field_simp
  have hfun : (fun t : ℝ => |1 / (2 * Real.cosh t ^ 2)| •
      (((logisticVar t : ℝ) : ℂ) ^ ((((s : ℂ) - (x : ℂ) * Complex.I) / 2) - 1) *
        ((1 : ℂ) - ((logisticVar t : ℝ) : ℂ)) ^ ((((s : ℂ) + (x : ℂ) * Complex.I) / 2) - 1)))
      = fun t : ℝ => (((2 : ℝ) ^ (1 - s) : ℝ) : ℂ) * ((((Real.cosh t) ^ (-s) : ℝ) : ℂ) *
        Complex.exp (-((x : ℂ) * (t : ℂ)) * Complex.I)) := funext hpt
  rw [MeasureTheory.setIntegral_univ, hfun, MeasureTheory.integral_const_mul,
    ← betaIntegral_eq_setIntegral] at hchange
  have hare : (0 : ℝ) < (((s : ℂ) - (x : ℂ) * Complex.I) / 2).re := by
    have h : ((s : ℂ) - (x : ℂ) * Complex.I) / 2
        = ((s / 2 : ℝ) : ℂ) - ((x / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one]
    linarith
  have hbre : (0 : ℝ) < (((s : ℂ) + (x : ℂ) * Complex.I) / 2).re := by
    have h : ((s : ℂ) + (x : ℂ) * Complex.I) / 2
        = ((s / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one]
    linarith
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hare hbre
  have hsum : (((s : ℂ) - (x : ℂ) * Complex.I) / 2) + (((s : ℂ) + (x : ℂ) * Complex.I) / 2)
      = (s : ℂ) := by ring
  rw [hsum] at hbeta
  have hGne : Complex.Gamma (s : ℂ) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n => ?_
    intro h
    have hre : ((s : ℂ)).re = (-(n : ℂ)).re := by rw [h]
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmul : ((2 : ℝ) ^ (s - 1) : ℝ) * ((2 : ℝ) ^ (1 - s) : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hB : Complex.betaIntegral (((s : ℂ) - (x : ℂ) * Complex.I) / 2)
      (((s : ℂ) + (x : ℂ) * Complex.I) / 2)
      = Complex.Gamma (((s : ℂ) - (x : ℂ) * Complex.I) / 2) *
        Complex.Gamma (((s : ℂ) + (x : ℂ) * Complex.I) / 2) / Complex.Gamma (s : ℂ) := by
    rw [eq_div_iff hGne]
    exact (mul_comm _ _).trans hbeta.symm
  rw [hB] at hchange
  rw [hchange, ← mul_assoc, ← Complex.ofReal_mul, hmul]
  simp

/-! ### Positivity of the transform -/

/-- The transform is the real nonnegative quantity `2^(s-1) |Γ((s+ix)/2)|²/Γ(s)`. -/
theorem integral_cosh_rpow_neg_mul_exp_eq_ofReal {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (∫ t : ℝ, (((Real.cosh t) ^ (-s) : ℝ) : ℂ) *
        Complex.exp (-((x : ℂ) * (t : ℂ)) * Complex.I))
      = ((((2 : ℝ) ^ (s - 1) *
          Complex.normSq (Complex.Gamma (((s : ℂ) + (x : ℂ) * Complex.I) / 2)) /
            Real.Gamma s : ℝ)) : ℂ) := by
  have hconj : ((s : ℂ) - (x : ℂ) * Complex.I) / 2
      = (starRingEnd ℂ) (((s : ℂ) + (x : ℂ) * Complex.I) / 2) := by
    simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply]
    constructor <;> ring
  rw [integral_cosh_rpow_neg_mul_exp hs x, hconj, Complex.Gamma_conj,
    mul_comm ((starRingEnd ℂ) _) _, Complex.mul_conj, Complex.Gamma_ofReal]
  have hG : (0 : ℝ) < Real.Gamma s := Real.Gamma_pos_of_pos hs
  push_cast
  field_simp

/-- The transform is nonnegative. -/
theorem integral_cosh_rpow_neg_mul_exp_nonneg {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 ≤ (2 : ℝ) ^ (s - 1) *
      Complex.normSq (Complex.Gamma (((s : ℂ) + (x : ℂ) * Complex.I) / 2)) / Real.Gamma s := by
  have hG : (0 : ℝ) < Real.Gamma s := Real.Gamma_pos_of_pos hs
  have hn : (0 : ℝ) ≤ Complex.normSq (Complex.Gamma (((s : ℂ) + (x : ℂ) * Complex.I) / 2)) :=
    Complex.normSq_nonneg _
  positivity

end

end HTGeometry
