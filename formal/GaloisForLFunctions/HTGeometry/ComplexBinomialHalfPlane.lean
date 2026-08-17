import GaloisForLFunctions.HTGeometry.ComplexBinomialRemainder

/-!
# The complex binomial remainder on the closed right half plane

On the disc of radius one half the base of a binomial power stays above one half in modulus; on the
closed right half plane it stays above *one*, which is sharper and, more importantly, carries no
restriction on the size of the argument.  The same induction -- differentiate, integrate back along
the segment to the origin, lower the exponent by one -- therefore gives a remainder bound valid on
the whole half plane, with the plain falling-factorial majorant.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section HalfPlaneBinomial

/-- The majorant of the complex Taylor remainder on the closed right half plane. -/
def cbinomHalfCoeff (α : ℝ) (m : ℕ) : ℝ :=
  (∏ j ∈ Finset.range m, |α - (j : ℝ)|) / (Nat.factorial m : ℝ)

theorem cbinomHalfCoeff_nonneg (α : ℝ) (m : ℕ) : 0 ≤ cbinomHalfCoeff α m :=
  div_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)

@[simp] theorem cbinomHalfCoeff_zero (α : ℝ) : cbinomHalfCoeff α 0 = 1 := by
  simp [cbinomHalfCoeff]

theorem cbinomHalfCoeff_succ (α : ℝ) (m : ℕ) :
    cbinomHalfCoeff α (m + 1) = |α| * cbinomHalfCoeff (α - 1) m / ((m : ℝ) + 1) := by
  have hprod : (∏ i ∈ Finset.range (m + 1), |α - (i : ℝ)|)
      = (∏ i ∈ Finset.range m, |(α - 1) - (i : ℝ)|) * |α| := by
    rw [Finset.prod_range_succ']
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      congr 1
      push_cast
      ring
    · simp
  have hfac : ((Nat.factorial (m + 1) : ℕ) : ℝ) = ((m : ℝ) + 1) * (Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfacm : ((Nat.factorial m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  rw [cbinomHalfCoeff, cbinomHalfCoeff, hprod, hfac]
  field_simp

theorem one_add_mem_slitPlane_of_re_nonneg {u : ℂ} (hu : 0 ≤ u.re) : 1 + u ∈ slitPlane := by
  refine Or.inl ?_
  have h : (1 + u).re = 1 + u.re := by simp
  rw [h]
  linarith

theorem one_le_norm_one_add_of_re_nonneg {u : ℂ} (hu : 0 ≤ u.re) : 1 ≤ ‖1 + u‖ := by
  have h := Complex.re_le_norm (1 + u)
  have h2 : (1 + u).re = 1 + u.re := by simp
  rw [h2] at h
  linarith

/-- The inductive step of the half-plane remainder bound, isolated so that it also covers exponents
between zero and one at every positive order. -/
theorem norm_cbinomRem_succ_le_of_pred_halfPlane {α : ℝ} (m : ℕ) {u : ℂ} (hu : 0 ≤ u.re)
    (ih : ∀ {v : ℂ}, 0 ≤ v.re → ‖cbinomRem (α - 1) m v‖ ≤ cbinomHalfCoeff (α - 1) m * ‖v‖ ^ m) :
    ‖cbinomRem α (m + 1) u‖ ≤ cbinomHalfCoeff α (m + 1) * ‖u‖ ^ (m + 1) := by
  have hseg : ∀ s : ℝ, s ∈ Set.uIcc (0 : ℝ) 1 → 0 ≤ ((s : ℂ) * u).re := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have h : ((s : ℂ) * u).re = s * u.re := by
      simp [Complex.mul_re]
    rw [h]
    exact mul_nonneg hs.1 hu
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => cbinomRem α (m + 1) ((r : ℂ) * u))
        (u * ((α : ℂ) * cbinomRem (α - 1) m ((s : ℂ) * u))) s := by
    intro s hs
    have hslit : 1 + (s : ℂ) * u ∈ slitPlane := one_add_mem_slitPlane_of_re_nonneg (hseg s hs)
    have hmulR : HasDerivAt (fun r : ℝ => (r : ℂ) * u) u s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const u
    have hc := (hasDerivAt_cbinomRem α m hslit).scomp s hmulR
    rw [smul_eq_mul] at hc
    exact hc
  have hcont : ContinuousOn
      (fun s : ℝ => u * ((α : ℂ) * cbinomRem (α - 1) m ((s : ℂ) * u)))
      (Set.uIcc (0 : ℝ) 1) := by
    intro s hs
    have hslit : 1 + (s : ℂ) * u ∈ slitPlane := one_add_mem_slitPlane_of_re_nonneg (hseg s hs)
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul continuousAt_const (ContinuousAt.mul continuousAt_const ?_)
    have hinner : ContinuousAt (fun r : ℝ => ((r : ℂ) * u)) s := by fun_prop
    exact ContinuousAt.comp (g := cbinomRem (α - 1) m) (f := fun r : ℝ => ((r : ℂ) * u))
      (continuousAt_cbinomRem (α - 1) m hslit) hinner
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simp only [Complex.ofReal_zero, zero_mul, Complex.ofReal_one, one_mul] at hFTC
  rw [cbinomRem_zero_arg, sub_zero] at hFTC
  have hbdd : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      ‖u * ((α : ℂ) * cbinomRem (α - 1) m ((s : ℂ) * u))‖
        ≤ (‖u‖ * (|α| * (cbinomHalfCoeff (α - 1) m * ‖u‖ ^ m))) * s ^ m := by
    intro s hs
    have hs' := hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs'
    have h1 := ih (hseg s hs)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hsn : ‖(s : ℂ) * u‖ = s * ‖u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs'.1]
    rw [hsn, mul_pow] at h1
    have hnn : (0 : ℝ) ≤ ‖u‖ * |α| := by positivity
    calc ‖u‖ * (|α| * ‖cbinomRem (α - 1) m ((s : ℂ) * u)‖)
        ≤ ‖u‖ * (|α| * (cbinomHalfCoeff (α - 1) m * (s ^ m * ‖u‖ ^ m))) := by gcongr
      _ = (‖u‖ * (|α| * (cbinomHalfCoeff (α - 1) m * ‖u‖ ^ m))) * s ^ m := by ring
  have hmajint : IntervalIntegrable
      (fun s : ℝ => (‖u‖ * (|α| * (cbinomHalfCoeff (α - 1) m * ‖u‖ ^ m))) * s ^ m)
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_pow m)).intervalIntegrable _ _
  have hint : ‖∫ s in (0 : ℝ)..1, u * ((α : ℂ) * cbinomRem (α - 1) m ((s : ℂ) * u))‖
      ≤ ∫ s in (0 : ℝ)..1,
          (‖u‖ * (|α| * (cbinomHalfCoeff (α - 1) m * ‖u‖ ^ m))) * s ^ m := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num)) ?_
    refine intervalIntegral.integral_mono_on (by norm_num)
      (hcont.norm.intervalIntegrable) hmajint ?_
    intro s hs
    exact hbdd s (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact hs)
  rw [← hFTC]
  refine le_trans hint (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_pow, cbinomHalfCoeff_succ]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **The complex Taylor remainder bound on the closed right half plane.** -/
theorem norm_cbinomRem_le_of_re_nonneg {α : ℝ} (hα : α ≤ 0) (m : ℕ) {u : ℂ} (hu : 0 ≤ u.re) :
    ‖cbinomRem α m u‖ ≤ cbinomHalfCoeff α m * ‖u‖ ^ m := by
  induction m generalizing α u with
  | zero =>
      have hge : (1 : ℝ) ≤ ‖1 + u‖ := one_le_norm_one_add_of_re_nonneg hu
      have hnorm : ‖(1 + u) ^ (α : ℂ)‖ = ‖1 + u‖ ^ α := Complex.norm_cpow_real _ α
      have hbnd : ‖1 + u‖ ^ α ≤ 1 := by
        have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) hge hα
        simpa using h
      rw [cbinomRem]
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one,
        cbinomHalfCoeff, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, div_one]
      rw [hnorm]
      exact hbnd
  | succ m ih =>
      exact norm_cbinomRem_succ_le_of_pred_halfPlane m hu (fun {v} hv => ih (by linarith) hv)

/-- **Every exponent at most one is covered at every positive order.** -/
theorem norm_cbinomRem_succ_le_of_re_nonneg {α : ℝ} (hα : α ≤ 1) (m : ℕ) {u : ℂ}
    (hu : 0 ≤ u.re) :
    ‖cbinomRem α (m + 1) u‖ ≤ cbinomHalfCoeff α (m + 1) * ‖u‖ ^ (m + 1) :=
  norm_cbinomRem_succ_le_of_pred_halfPlane m hu
    (fun {v} hv => norm_cbinomRem_le_of_re_nonneg (by linarith) m hv)

end HalfPlaneBinomial

end

end GaloisForLFunctions.HTGeometry
