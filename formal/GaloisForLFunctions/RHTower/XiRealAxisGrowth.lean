import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.HTGeometry.GammaLogGrowth

/-!
# The completed zeta function is not of exponential type

Along the even integers the completed function factors as

```
xi (2(m+1)) = (m+1)(2m+1) · π^{-(m+1)} · m! · ζ(2(m+1)),
```

and `ζ` is at least `1` there because its Dirichlet series has nonnegative terms and first term one.
The factorial therefore forces

```
log ‖xi (2(m+1))‖ / (2(m+1)) → ∞,
```

so no bound `log ‖xi s‖ ≤ C‖s‖` can hold.  This is the growth input that a genus-zero — that is,
first-power summable — zero divisor would contradict.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- On the natural numbers beyond one the zeta values have norm at least one: the Dirichlet series
has nonnegative real terms and its first term is `1`. -/
theorem one_le_norm_riemannZeta_natCast {k : ℕ} (hk : 1 < k) :
    1 ≤ ‖riemannZeta (k : ℂ)‖ := by
  have hsumR : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ k) := Real.summable_one_div_nat_pow.mpr hk
  have hnorm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ k‖ = 1 / ((n : ℝ)) ^ k := by
    intro n
    rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
  have hsumC : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ k) := by
    refine Summable.of_norm ?_
    simpa [hnorm] using hsumR
  have hterm : ∀ n : ℕ, ((1 : ℂ) / (n : ℂ) ^ k).re = 1 / ((n : ℝ)) ^ k := by
    intro n
    have hcast : ((1 : ℂ) / (n : ℂ) ^ k) = ((1 / ((n : ℝ)) ^ k : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.ofReal_re]
  have hre : (riemannZeta (k : ℂ)).re = ∑' n : ℕ, 1 / ((n : ℝ)) ^ k := by
    rw [zeta_nat_eq_tsum_of_gt_one hk, Complex.re_tsum hsumC]
    exact tsum_congr hterm
  have hge : (1 : ℝ) ≤ ∑' n : ℕ, 1 / ((n : ℝ)) ^ k := by
    have hterm1 : 1 / (((1 : ℕ) : ℝ)) ^ k ≤ ∑' n : ℕ, 1 / ((n : ℝ)) ^ k :=
      hsumR.le_tsum 1 fun n _ => by positivity
    simpa using hterm1
  calc (1 : ℝ) ≤ (riemannZeta (k : ℂ)).re := by rw [hre]; exact hge
    _ ≤ ‖riemannZeta (k : ℂ)‖ := Complex.re_le_norm _

/-- Away from the two poles the tower's `xi` is the classical completed product. -/
theorem xi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs1'' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [xi, completedRiemannZeta_eq]
  field_simp
  ring

/-- The archimedean factor is nonvanishing in the right half-plane, so the completed function is the
product of that factor with `ζ`. -/
theorem completedRiemannZeta_eq_Gammaℝ_mul {s : ℂ} (hspos : 0 < s.re) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hspos
    norm_num at hspos
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hspos]

/-- Explicit archimedean factor at an even integer. -/
theorem Gammaℝ_two_mul_natSucc (m : ℕ) :
    Complex.Gammaℝ (2 * ((m : ℂ) + 1))
      = (Real.pi : ℂ) ^ (-((m : ℂ) + 1)) * (m.factorial : ℂ) := by
  rw [Complex.Gammaℝ]
  congr 1
  · congr 1
    ring
  · rw [show (2 * ((m : ℂ) + 1)) / 2 = (m : ℂ) + 1 by ring, Complex.Gamma_nat_eq_factorial]

/-- **Factorial lower bound for `xi` on the even integers.** -/
theorem factorial_mul_rpow_le_norm_xi (m : ℕ) :
    (m.factorial : ℝ) * Real.pi ^ (-((m : ℝ) + 1)) ≤ ‖xi (2 * ((m : ℂ) + 1))‖ := by
  set s : ℂ := 2 * ((m : ℂ) + 1) with hs
  have hsre : s.re = 2 * ((m : ℝ) + 1) := by
    simp [hs]
  have hspos : 0 < s.re := by rw [hsre]; positivity
  have hre2 : (2 : ℝ) ≤ s.re := by
    rw [hsre]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hre2
    norm_num at hre2
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre2
    norm_num at hre2
  have hnat : s = ((2 * (m + 1) : ℕ) : ℂ) := by push_cast [hs]; ring
  have hzeta : 1 ≤ ‖riemannZeta s‖ := by
    rw [hnat]
    exact one_le_norm_riemannZeta_natCast (by omega)
  have hfac : xi s = s * (s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s) := by
    rw [xi_eq_mul_completedRiemannZeta hs0 hs1, completedRiemannZeta_eq_Gammaℝ_mul hspos]
  have hGam : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-((m : ℂ) + 1)) * (m.factorial : ℂ) :=
    Gammaℝ_two_mul_natSucc m
  have hpiNorm : ‖(Real.pi : ℂ) ^ (-((m : ℂ) + 1))‖ = Real.pi ^ (-((m : ℝ) + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    norm_num
  have hcoef : (1 : ℝ) ≤ ‖s * (s - 1) / 2‖ := by
    have hval : s * (s - 1) / 2 = ((( (m : ℝ) + 1) * (2 * (m : ℝ) + 1) : ℝ) : ℂ) := by
      rw [hs]; push_cast; ring
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  rw [hfac]
  rw [norm_mul, norm_mul, hGam, norm_mul, hpiNorm, Complex.norm_natCast]
  have hpipos : (0 : ℝ) < Real.pi ^ (-((m : ℝ) + 1)) := Real.rpow_pos_of_pos Real.pi_pos _
  have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  calc (m.factorial : ℝ) * Real.pi ^ (-((m : ℝ) + 1))
      = 1 * (Real.pi ^ (-((m : ℝ) + 1)) * (m.factorial : ℝ)) * 1 := by ring
    _ ≤ ‖s * (s - 1) / 2‖ * (Real.pi ^ (-((m : ℝ) + 1)) * (m.factorial : ℝ))
          * ‖riemannZeta s‖ := by
        apply mul_le_mul _ hzeta (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = ‖s * (s - 1) / 2‖ * (Real.pi ^ (-((m : ℝ) + 1)) * (m.factorial : ℝ)
          * ‖riemannZeta s‖) := by ring

/-- Logarithmic form of the growth bound. -/
theorem log_sub_le_log_norm_xi (m : ℕ) :
    Real.log m.factorial - ((m : ℝ) + 1) * Real.log Real.pi
      ≤ Real.log ‖xi (2 * ((m : ℂ) + 1))‖ := by
  have hpos : (0 : ℝ) < (m.factorial : ℝ) * Real.pi ^ (-((m : ℝ) + 1)) := by
    have : (0 : ℝ) < Real.pi ^ (-((m : ℝ) + 1)) := Real.rpow_pos_of_pos Real.pi_pos _
    positivity
  have hle := factorial_mul_rpow_le_norm_xi m
  have hlog := Real.log_le_log hpos hle
  have hval : Real.log ((m.factorial : ℝ) * Real.pi ^ (-((m : ℝ) + 1)))
      = Real.log m.factorial - ((m : ℝ) + 1) * Real.log Real.pi := by
    rw [Real.log_mul (by positivity) (ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)),
      Real.log_rpow Real.pi_pos]
    ring
  rwa [hval] at hlog

/-- **`xi` is not of exponential type.**  The normalized logarithm of `xi` along the even integers
tends to infinity. -/
theorem tendsto_log_norm_xi_div_atTop :
    Tendsto (fun m : ℕ => Real.log ‖xi (2 * ((m : ℂ) + 1))‖ / (2 * ((m : ℝ) + 1)))
      atTop atTop := by
  have hnat : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun m : ℕ => Real.log m) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hminor : ∀ᶠ m : ℕ in atTop,
      (Real.log m - 1) / 4 - Real.log Real.pi / 2
        ≤ Real.log ‖xi (2 * ((m : ℂ) + 1))‖ / (2 * ((m : ℝ) + 1)) := by
    filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop (1 : ℝ)] with m hm hlm
    have hm0 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hden : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hden]
    have hfacbnd := GaloisForLFunctions.HTGeometry.natMul_log_sub_one_le_log_factorial m
    have hbase := log_sub_le_log_norm_xi m
    have hprod : 0 ≤ (Real.log m - 1) * ((m : ℝ) - 1) :=
      mul_nonneg (sub_nonneg.mpr hlm) (sub_nonneg.mpr hm0)
    have hstep : ((Real.log m - 1) / 4 - Real.log Real.pi / 2) * (2 * ((m : ℝ) + 1))
        ≤ (m : ℝ) * (Real.log m - 1) - ((m : ℝ) + 1) * Real.log Real.pi := by
      nlinarith [hm0, hlm, hprod]
    linarith [hbase, hfacbnd, hstep]
  refine tendsto_atTop_mono' atTop hminor ?_
  have h1 : Tendsto (fun m : ℕ => (Real.log m - 1) / 4) atTop atTop := by
    have := tendsto_atTop_add_const_right atTop (-1 : ℝ) hlog
    simpa [sub_eq_add_neg] using this.atTop_div_const (by norm_num : (0:ℝ) < 4)
  simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop
    (-(Real.log Real.pi / 2)) h1

/-- No linear majorant: for every constant the logarithm of `xi` eventually exceeds it. -/
theorem eventually_lt_log_norm_xi (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, C * (2 * ((m : ℝ) + 1)) < Real.log ‖xi (2 * ((m : ℂ) + 1))‖ := by
  filter_upwards [tendsto_log_norm_xi_div_atTop.eventually_gt_atTop C] with m hm
  have hden : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
  rw [lt_div_iff₀ hden] at hm
  linarith

end

end RHTower
