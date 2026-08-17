import GaloisForLFunctions.HTGeometry.HalfShiftedBinomialRemainder

/-!
# Taylor remainders of the complex binomial power

The same induction that bounds the Taylor remainder of `(1+s)^α` on the real half line works on the
complex disc of radius one half: the derivative lowers the exponent by one, the modulus of the power
is the power of the modulus, and integrating back along the segment from the origin gives the bound
with one more power of the argument and one more factorial in the denominator.

This is the tool that converts an expansion in a spectral parameter into an expansion in a
frequency-shifted parameter, where the shift is complex.
-/

open Complex Set

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section ComplexBinomial

/-- The generalized binomial coefficient at a real exponent. -/
def cbinomCoeff (α : ℝ) (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range k, (α - (j : ℝ))) / (Nat.factorial k : ℝ)

/-- The Taylor remainder of the complex binomial power. -/
def cbinomRem (α : ℝ) (m : ℕ) (u : ℂ) : ℂ :=
  (1 + u) ^ (α : ℂ) - ∑ k ∈ Finset.range m, ((cbinomCoeff α k : ℝ) : ℂ) * u ^ k

/-- The absolute majorant of the complex Taylor remainder. -/
def cbinomAbsCoeff (α : ℝ) (m : ℕ) : ℝ :=
  (∏ j ∈ Finset.range m, |α - (j : ℝ)|) / (Nat.factorial m : ℝ) * (2 : ℝ) ^ ((m : ℝ) - α)

@[simp] theorem cbinomCoeff_zero (α : ℝ) : cbinomCoeff α 0 = 1 := by simp [cbinomCoeff]

theorem cbinomAbsCoeff_nonneg (α : ℝ) (m : ℕ) : 0 ≤ cbinomAbsCoeff α m := by
  refine mul_nonneg (div_nonneg (Finset.prod_nonneg fun j _ => abs_nonneg _) ?_) ?_
  · positivity
  · positivity

theorem cbinomCoeff_succ (α : ℝ) (j : ℕ) :
    ((j : ℝ) + 1) * cbinomCoeff α (j + 1) = α * cbinomCoeff (α - 1) j := by
  have hprod : (∏ i ∈ Finset.range (j + 1), (α - (i : ℝ)))
      = (∏ i ∈ Finset.range j, ((α - 1) - (i : ℝ))) * α := by
    rw [Finset.prod_range_succ']
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      push_cast
      ring
    · simp
  have hfac : ((Nat.factorial (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) * (Nat.factorial j : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfacj : ((Nat.factorial j : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  rw [cbinomCoeff, cbinomCoeff, hprod, hfac]
  field_simp

theorem cbinomAbsCoeff_succ (α : ℝ) (m : ℕ) :
    cbinomAbsCoeff α (m + 1) = |α| * cbinomAbsCoeff (α - 1) m / ((m : ℝ) + 1) := by
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
  rw [cbinomAbsCoeff, cbinomAbsCoeff, hprod, hfac]
  push_cast
  rw [show ((m : ℝ) + 1) - α = (m : ℝ) - (α - 1) by ring]
  field_simp

theorem cbinomRem_zero_arg (α : ℝ) (m : ℕ) : cbinomRem α (m + 1) 0 = 0 := by
  rw [cbinomRem, Finset.sum_range_succ']
  simp [Complex.one_cpow]

theorem hasDerivAt_cbinomRem (α : ℝ) (m : ℕ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    HasDerivAt (cbinomRem α (m + 1)) ((α : ℂ) * cbinomRem (α - 1) m z) z := by
  have hbase : HasDerivAt (fun u : ℂ => (1 + u) ^ (α : ℂ))
      ((α : ℂ) * (1 + z) ^ ((α : ℂ) - 1)) z := by
    have h1 : HasDerivAt (fun u : ℂ => 1 + u) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h := h1.cpow_const (c := (α : ℂ)) hz
    simpa using h
  have hterm : ∀ j ∈ Finset.range m,
      HasDerivAt (fun u : ℂ => ((cbinomCoeff α (j + 1) : ℝ) : ℂ) * u ^ (j + 1))
        ((α : ℂ) * (((cbinomCoeff (α - 1) j : ℝ) : ℂ) * z ^ j)) z := by
    intro j _
    have h := (hasDerivAt_pow (j + 1) z).const_mul (((cbinomCoeff α (j + 1) : ℝ) : ℂ))
    have hval : ((cbinomCoeff α (j + 1) : ℝ) : ℂ) * (((j : ℕ) + 1 : ℕ) * z ^ (j + 1 - 1))
        = (α : ℂ) * (((cbinomCoeff (α - 1) j : ℝ) : ℂ) * z ^ j) := by
      have hc := cbinomCoeff_succ α j
      have hc' : ((j : ℂ) + 1) * ((cbinomCoeff α (j + 1) : ℝ) : ℂ)
          = (α : ℂ) * ((cbinomCoeff (α - 1) j : ℝ) : ℂ) := by
        exact_mod_cast congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hc
      push_cast
      linear_combination (z ^ j) * hc'
    rw [← hval]
    exact h
  have hsum0 := HasDerivAt.sum hterm
  have hfun : (∑ i ∈ Finset.range m, fun u : ℂ =>
      ((cbinomCoeff α (i + 1) : ℝ) : ℂ) * u ^ (i + 1))
      = fun u : ℂ => ∑ j ∈ Finset.range m, ((cbinomCoeff α (j + 1) : ℝ) : ℂ) * u ^ (j + 1) := by
    funext u
    simp [Finset.sum_apply]
  rw [hfun] at hsum0
  have hconst : HasDerivAt (fun u : ℂ => ((cbinomCoeff α 0 : ℝ) : ℂ) * u ^ 0) 0 z := by
    simpa using (hasDerivAt_const z (((cbinomCoeff α 0 : ℝ) : ℂ) * (1 : ℂ)))
  have hadd := hsum0.add hconst
  rw [add_zero, ← Finset.mul_sum] at hadd
  have hfun2 : ((fun u : ℂ => ∑ j ∈ Finset.range m,
      ((cbinomCoeff α (j + 1) : ℝ) : ℂ) * u ^ (j + 1))
      + fun u : ℂ => ((cbinomCoeff α 0 : ℝ) : ℂ) * u ^ 0)
      = fun u : ℂ => ∑ k ∈ Finset.range (m + 1), ((cbinomCoeff α k : ℝ) : ℂ) * u ^ k := by
    funext u
    simp only [Pi.add_apply]
    rw [Finset.sum_range_succ']
  rw [hfun2] at hadd
  have hcomb := hbase.sub hadd
  have hval : (α : ℂ) * (1 + z) ^ ((α : ℂ) - 1)
      - (α : ℂ) * ∑ j ∈ Finset.range m, ((cbinomCoeff (α - 1) j : ℝ) : ℂ) * z ^ j
      = (α : ℂ) * cbinomRem (α - 1) m z := by
    rw [cbinomRem, show (((α - 1 : ℝ)) : ℂ) = (α : ℂ) - 1 by push_cast; ring]
    ring
  have hfn : cbinomRem α (m + 1)
      = (fun u : ℂ => (1 + u) ^ (α : ℂ)) - fun u : ℂ =>
          ∑ k ∈ Finset.range (m + 1), ((cbinomCoeff α k : ℝ) : ℂ) * u ^ k := by
    funext u
    simp only [Pi.sub_apply, cbinomRem]
  rw [hfn, ← hval]
  exact hcomb

theorem continuousAt_cbinomRem (α : ℝ) (m : ℕ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    ContinuousAt (cbinomRem α m) z := by
  refine ContinuousAt.sub ?_ (by fun_prop)
  have h1 : HasDerivAt (fun u : ℂ => 1 + u) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  exact (h1.cpow_const hz).continuousAt

theorem one_add_mem_slitPlane_of_norm_le_half {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) : 1 + u ∈ slitPlane := by
  refine Or.inl ?_
  have h1 : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
  have h2 : (1 + u).re = 1 + u.re := by simp
  rw [h2]
  have := abs_le.mp h1
  linarith [this.1]

/-- The inductive step of the complex remainder bound, isolated so that it also covers exponents
between zero and one at every positive order. -/
theorem norm_cbinomRem_succ_le_of_pred {α : ℝ} (m : ℕ) {u : ℂ} (hu : ‖u‖ ≤ 1 / 2)
    (ih : ∀ {v : ℂ}, ‖v‖ ≤ 1 / 2 → ‖cbinomRem (α - 1) m v‖ ≤ cbinomAbsCoeff (α - 1) m * ‖v‖ ^ m) :
    ‖cbinomRem α (m + 1) u‖ ≤ cbinomAbsCoeff α (m + 1) * ‖u‖ ^ (m + 1) := by

  have hseg : ∀ s : ℝ, s ∈ Set.uIcc (0 : ℝ) 1 → ‖(s : ℂ) * u‖ ≤ 1 / 2 := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
    nlinarith [norm_nonneg u, hs.2, hu]
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => cbinomRem α (m + 1) ((r : ℂ) * u))
        (u * ((α : ℂ) * cbinomRem (α - 1) m ((s : ℂ) * u))) s := by
    intro s hs
    have hslit : 1 + (s : ℂ) * u ∈ slitPlane := one_add_mem_slitPlane_of_norm_le_half (hseg s hs)
    have hmulR : HasDerivAt (fun r : ℝ => (r : ℂ) * u) u s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const u
    have hc := (hasDerivAt_cbinomRem α m hslit).scomp s hmulR
    rw [smul_eq_mul] at hc
    exact hc
  have hcont : ContinuousOn
      (fun s : ℝ => u * ((α : ℂ) * cbinomRem (α - 1) m ((s : ℂ) * u)))
      (Set.uIcc (0 : ℝ) 1) := by
    intro s hs
    have hslit : 1 + (s : ℂ) * u ∈ slitPlane := one_add_mem_slitPlane_of_norm_le_half (hseg s hs)
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul continuousAt_const (ContinuousAt.mul continuousAt_const ?_)
    have hinner : ContinuousAt (fun r : ℝ => ((r : ℂ) * u)) s := by fun_prop
    have hcc := ContinuousAt.comp (g := cbinomRem (α - 1) m) (f := fun r : ℝ => ((r : ℂ) * u))
      (continuousAt_cbinomRem (α - 1) m hslit) hinner
    exact hcc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  simp only [Complex.ofReal_zero, zero_mul, Complex.ofReal_one, one_mul] at hFTC
  rw [cbinomRem_zero_arg, sub_zero] at hFTC
  have hbdd : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      ‖u * ((α : ℂ) * cbinomRem (α - 1) m ((s : ℂ) * u))‖
        ≤ (‖u‖ * (|α| * (cbinomAbsCoeff (α - 1) m * ‖u‖ ^ m))) * s ^ m := by
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
        ≤ ‖u‖ * (|α| * (cbinomAbsCoeff (α - 1) m * (s ^ m * ‖u‖ ^ m))) := by
          gcongr
      _ = (‖u‖ * (|α| * (cbinomAbsCoeff (α - 1) m * ‖u‖ ^ m))) * s ^ m := by ring
  have hmajint : IntervalIntegrable
      (fun s : ℝ => (‖u‖ * (|α| * (cbinomAbsCoeff (α - 1) m * ‖u‖ ^ m))) * s ^ m)
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_pow m)).intervalIntegrable _ _
  have hint : ‖∫ s in (0 : ℝ)..1, u * ((α : ℂ) * cbinomRem (α - 1) m ((s : ℂ) * u))‖
      ≤ ∫ s in (0 : ℝ)..1,
          (‖u‖ * (|α| * (cbinomAbsCoeff (α - 1) m * ‖u‖ ^ m))) * s ^ m := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num)) ?_
    refine intervalIntegral.integral_mono_on (by norm_num)
      (hcont.norm.intervalIntegrable) hmajint ?_
    intro s hs
    exact hbdd s (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact hs)
  rw [← hFTC]
  refine le_trans hint (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_pow, cbinomAbsCoeff_succ]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring


/-- **The complex Taylor remainder bound on the disc of radius one half.** -/
theorem norm_cbinomRem_le {α : ℝ} (hα : α ≤ 0) (m : ℕ) {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖cbinomRem α m u‖ ≤ cbinomAbsCoeff α m * ‖u‖ ^ m := by
  induction m generalizing α u with
  | zero =>
      have hge : (1 : ℝ) / 2 ≤ ‖1 + u‖ := by
        have h := norm_sub_norm_le (1 : ℂ) (-u)
        have hn : ‖(-u : ℂ)‖ = ‖u‖ := norm_neg u
        have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
        have h2 : (1 : ℂ) - -u = 1 + u := by ring
        rw [h2, h1, hn] at h
        linarith
      have hnorm : ‖(1 + u) ^ (α : ℂ)‖ = ‖1 + u‖ ^ α := Complex.norm_cpow_real _ α
      have hbnd : ‖1 + u‖ ^ α ≤ (2 : ℝ) ^ (-α) := by
        have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) hge hα
        refine le_trans h (le_of_eq ?_)
        rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by
          rw [Real.rpow_neg_one]; norm_num, ← Real.rpow_mul (by norm_num)]
        ring_nf
      rw [cbinomRem]
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, mul_one,
        cbinomAbsCoeff, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, div_one,
        one_mul, Nat.cast_zero, zero_sub]
      rw [hnorm]
      exact hbnd
  | succ m ih =>
      exact norm_cbinomRem_succ_le_of_pred m hu (fun {v} hv => ih (by linarith) hv)

/-- **Every exponent at most one is covered at every positive order.** -/
theorem norm_cbinomRem_succ_le {α : ℝ} (hα : α ≤ 1) (m : ℕ) {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖cbinomRem α (m + 1) u‖ ≤ cbinomAbsCoeff α (m + 1) * ‖u‖ ^ (m + 1) :=
  norm_cbinomRem_succ_le_of_pred m hu (fun {v} hv => norm_cbinomRem_le (by linarith) m hv)

end ComplexBinomial

end

end GaloisForLFunctions.HTGeometry
