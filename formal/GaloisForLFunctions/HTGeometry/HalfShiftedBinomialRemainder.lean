import GaloisForLFunctions.HTGeometry.WatsonGaussianRemainder

/-!
# Taylor remainders of the half-shifted power

The `m`-th derivative of `(1 + s/2)^α` is the falling factorial of `α` over `2^m`, times the same
power at exponent `α - m`.  On the half line every such power is at most one when the exponent is
nonpositive, so a single induction -- differentiate, integrate back, and lower the exponent by one --
bounds the Taylor remainder by the falling factorial times `(s/2)^m/m!`, with no restriction to a
disc of convergence.

At exponent `-1/2` the falling factorial is at most `m!`, so the remainder is at most `(s/2)^m` on
the whole half line.  That is the profile input of Watson's lemma for the Schläfli representation of
the modified Bessel function of order one.
-/

open Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section HalfShifted

/-- The generalized binomial coefficient of the half-shifted power `(1 + s/2)^α`. -/
def binomCoeff (α : ℝ) (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range k, (α - (j : ℝ))) / (2 ^ k * (Nat.factorial k : ℝ))

/-- The Taylor remainder of `(1 + s/2)^α` at order `m`. -/
def binomRem (α : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  (1 + s / 2) ^ α - ∑ k ∈ Finset.range m, binomCoeff α k * s ^ k

/-- The absolute majorant of the generalized binomial coefficient. -/
def binomAbsCoeff (α : ℝ) (m : ℕ) : ℝ :=
  (∏ j ∈ Finset.range m, |α - (j : ℝ)|) / (2 ^ m * (Nat.factorial m : ℝ))

@[simp] theorem binomCoeff_zero (α : ℝ) : binomCoeff α 0 = 1 := by
  simp [binomCoeff]

@[simp] theorem binomAbsCoeff_zero (α : ℝ) : binomAbsCoeff α 0 = 1 := by
  simp [binomAbsCoeff]

theorem binomAbsCoeff_nonneg (α : ℝ) (m : ℕ) : 0 ≤ binomAbsCoeff α m := by
  refine div_nonneg (Finset.prod_nonneg fun j _ => abs_nonneg _) ?_
  positivity

theorem binomCoeff_succ (α : ℝ) (j : ℕ) :
    ((j : ℝ) + 1) * binomCoeff α (j + 1) = (α / 2) * binomCoeff (α - 1) j := by
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
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hfacj : ((Nat.factorial j : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  rw [binomCoeff, binomCoeff, hprod, hfac]
  field_simp
  ring

theorem binomAbsCoeff_succ (α : ℝ) (m : ℕ) :
    binomAbsCoeff α (m + 1) = (|α| / 2) * binomAbsCoeff (α - 1) m / ((m : ℝ) + 1) := by
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
  rw [binomAbsCoeff, binomAbsCoeff, hprod, hfac]
  field_simp
  ring

theorem hasDerivAt_shiftRpow (α : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun u : ℝ => (1 + u / 2) ^ α)
      (α * (1 + s / 2) ^ (α - 1) * (1 / 2)) s := by
  have hpos : (0 : ℝ) < 1 + s / 2 := by linarith
  have h1 : HasDerivAt (fun u : ℝ => 1 + u / 2) (1 / 2) s := by
    simpa using ((hasDerivAt_id s).div_const 2).const_add 1
  exact (Real.hasDerivAt_rpow_const (p := α) (Or.inl (ne_of_gt hpos))).comp s h1

theorem binomRem_zero_arg (α : ℝ) (m : ℕ) : binomRem α (m + 1) 0 = 0 := by
  rw [binomRem, Finset.sum_range_succ']
  simp

theorem hasDerivAt_binomRem (α : ℝ) (m : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (binomRem α (m + 1)) ((α / 2) * binomRem (α - 1) m s) s := by
  have hbase := hasDerivAt_shiftRpow α hs
  have hsum : HasDerivAt (fun u : ℝ => ∑ k ∈ Finset.range (m + 1), binomCoeff α k * u ^ k)
      ((α / 2) * ∑ j ∈ Finset.range m, binomCoeff (α - 1) j * s ^ j) s := by
    have hrw : (fun u : ℝ => ∑ k ∈ Finset.range (m + 1), binomCoeff α k * u ^ k)
        = fun u : ℝ => (∑ j ∈ Finset.range m, binomCoeff α (j + 1) * u ^ (j + 1))
          + binomCoeff α 0 * u ^ 0 := by
      funext u
      rw [Finset.sum_range_succ']
    rw [hrw]
    have hterm : ∀ j ∈ Finset.range m,
        HasDerivAt (fun u : ℝ => binomCoeff α (j + 1) * u ^ (j + 1))
          ((α / 2) * (binomCoeff (α - 1) j * s ^ j)) s := by
      intro j _
      have h := ((hasDerivAt_pow (j + 1) s).const_mul (binomCoeff α (j + 1)))
      have hval : binomCoeff α (j + 1) * (((j : ℕ) + 1 : ℕ) * s ^ (j + 1 - 1))
          = (α / 2) * (binomCoeff (α - 1) j * s ^ j) := by
        have hc := binomCoeff_succ α j
        push_cast
        linear_combination (s ^ j) * hc
      rw [← hval]
      exact h
    have hsum0 := HasDerivAt.sum hterm
    have hfun : (∑ i ∈ Finset.range m, fun u : ℝ => binomCoeff α (i + 1) * u ^ (i + 1))
        = fun u : ℝ => ∑ j ∈ Finset.range m, binomCoeff α (j + 1) * u ^ (j + 1) := by
      funext u
      simp [Finset.sum_apply]
    rw [hfun] at hsum0
    have hsum' : HasDerivAt (fun u : ℝ => ∑ j ∈ Finset.range m,
        binomCoeff α (j + 1) * u ^ (j + 1))
        (∑ j ∈ Finset.range m, (α / 2) * (binomCoeff (α - 1) j * s ^ j)) s := hsum0
    have hconst : HasDerivAt (fun u : ℝ => binomCoeff α 0 * u ^ 0) 0 s := by
      simpa using (hasDerivAt_const s (binomCoeff α 0 * (1 : ℝ)))
    have hadd := hsum'.add hconst
    rw [add_zero, ← Finset.mul_sum] at hadd
    exact hadd
  have hcomb := hbase.sub hsum
  have hval : α * (1 + s / 2) ^ (α - 1) * (1 / 2)
      - (α / 2) * ∑ j ∈ Finset.range m, binomCoeff (α - 1) j * s ^ j
      = (α / 2) * binomRem (α - 1) m s := by
    rw [binomRem]
    ring
  rw [← hval]
  exact hcomb

theorem continuousOn_binomRem (α : ℝ) (m : ℕ) : ContinuousOn (binomRem α m) (Ici 0) := by
  refine ContinuousOn.sub ?_ (by fun_prop)
  intro s hs
  exact (hasDerivAt_shiftRpow α hs).continuousAt.continuousWithinAt

/-- **The Taylor remainder bound on the whole half line.** -/
theorem abs_binomRem_le (m : ℕ) {α : ℝ} (hα : α ≤ 0) {s : ℝ} (hs : 0 ≤ s) :
    |binomRem α m s| ≤ binomAbsCoeff α m * s ^ m := by
  induction m generalizing α s with
  | zero =>
      have hbase : (0 : ℝ) ≤ (1 + s / 2) ^ α := Real.rpow_nonneg (by linarith) α
      have hle : (1 + s / 2) ^ α ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hα
      rw [binomRem]
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, binomAbsCoeff_zero, pow_zero,
        one_mul]
      rw [abs_of_nonneg hbase]
      exact hle
  | succ m ih =>
      have hderiv : ∀ u ∈ uIcc (0 : ℝ) s,
          HasDerivAt (binomRem α (m + 1)) ((α / 2) * binomRem (α - 1) m u) u := by
        intro u hu
        rw [uIcc_of_le hs] at hu
        exact hasDerivAt_binomRem α m hu.1
      have hcont : ContinuousOn (fun u : ℝ => (α / 2) * binomRem (α - 1) m u) (uIcc 0 s) := by
        rw [uIcc_of_le hs]
        exact continuousOn_const.mul ((continuousOn_binomRem (α - 1) m).mono fun u hu => hu.1)
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        hcont.intervalIntegrable
      rw [binomRem_zero_arg, sub_zero] at hFTC
      have hbdd : ∀ u ∈ uIcc (0 : ℝ) s,
          |(α / 2) * binomRem (α - 1) m u|
            ≤ (|α| / 2) * binomAbsCoeff (α - 1) m * u ^ m := by
        intro u hu
        rw [uIcc_of_le hs] at hu
        rw [abs_mul, abs_div, show |(2 : ℝ)| = 2 from by norm_num]
        have h1 := ih (α := α - 1) (by linarith) (s := u) hu.1
        have hnn : (0 : ℝ) ≤ |α| / 2 := by positivity
        calc |α| / 2 * |binomRem (α - 1) m u|
            ≤ |α| / 2 * (binomAbsCoeff (α - 1) m * u ^ m) :=
              mul_le_mul_of_nonneg_left h1 hnn
          _ = |α| / 2 * binomAbsCoeff (α - 1) m * u ^ m := by ring
      have hmajint : IntervalIntegrable
          (fun u : ℝ => (|α| / 2) * binomAbsCoeff (α - 1) m * u ^ m) volume 0 s :=
        (continuous_const.mul (continuous_pow m)).intervalIntegrable _ _
      have hint : |∫ u in (0 : ℝ)..s, (α / 2) * binomRem (α - 1) m u|
          ≤ ∫ u in (0 : ℝ)..s, (|α| / 2) * binomAbsCoeff (α - 1) m * u ^ m := by
        refine le_trans (intervalIntegral.abs_integral_le_integral_abs hs) ?_
        refine intervalIntegral.integral_mono_on hs
          (hcont.abs.intervalIntegrable) hmajint ?_
        intro u hu
        exact hbdd u (by rw [uIcc_of_le hs]; exact hu)
      rw [← hFTC]
      refine le_trans hint (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul, integral_pow, binomAbsCoeff_succ]
      have hfac : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring

theorem prod_range_add_one_real (n : ℕ) :
    (∏ i ∈ Finset.range n, ((i : ℝ) + 1)) = (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
      push_cast
      ring

theorem binomAbsCoeff_neg_half_le (m : ℕ) : binomAbsCoeff (-1 / 2 : ℝ) m ≤ 1 / 2 ^ m := by
  have hfacpos : (0 : ℝ) < (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hterm : ∀ j ∈ Finset.range m, |(-1 / 2 : ℝ) - (j : ℝ)| ≤ (j : ℝ) + 1 := by
    intro j _
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hprod : (∏ j ∈ Finset.range m, |(-1 / 2 : ℝ) - (j : ℝ)|) ≤ (Nat.factorial m : ℝ) := by
    calc (∏ j ∈ Finset.range m, |(-1 / 2 : ℝ) - (j : ℝ)|)
        ≤ ∏ j ∈ Finset.range m, ((j : ℝ) + 1) :=
          Finset.prod_le_prod (fun j _ => abs_nonneg _) hterm
      _ = (Nat.factorial m : ℝ) := prod_range_add_one_real m
  rw [binomAbsCoeff, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∏ j ∈ Finset.range m, |(-1 / 2 : ℝ) - (j : ℝ)|) * 2 ^ m
      ≤ (Nat.factorial m : ℝ) * 2 ^ m := by
        exact mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = 1 * (2 ^ m * (Nat.factorial m : ℝ)) := by ring

/-- **The remainder of the inverse square root on the whole half line.** -/
theorem abs_binomRem_neg_half_le (m : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |binomRem (-1 / 2 : ℝ) m s| ≤ (s / 2) ^ m := by
  refine le_trans (abs_binomRem_le m (by norm_num) hs) ?_
  calc binomAbsCoeff (-1 / 2 : ℝ) m * s ^ m ≤ (1 / 2 ^ m) * s ^ m :=
        mul_le_mul_of_nonneg_right (binomAbsCoeff_neg_half_le m) (by positivity)
    _ = (s / 2) ^ m := by rw [div_pow]; ring

end HalfShifted

section SchlafliProfile

/-- The Taylor coefficients of the Schläfli profile in the squared variable. -/
def schlafliCoeff (k : ℕ) : ℝ :=
  (Real.sqrt 2)⁻¹ * (binomCoeff (-1 / 2 : ℝ) k
    + (if k = 0 then 0 else binomCoeff (-1 / 2 : ℝ) (k - 1)))

theorem besselLaplaceProfile_eq_shifted (v : ℝ) :
    _root_.HTGeometry.besselLaplaceProfile v
      = (Real.sqrt 2)⁻¹ * ((1 + v ^ 2) * (1 + v ^ 2 / 2) ^ (-1 / 2 : ℝ)) := by
  rw [_root_.HTGeometry.besselLaplaceProfile]
  have hpos : (0 : ℝ) < 1 + v ^ 2 / 2 := by positivity
  have hsq : (2 : ℝ) + v ^ 2 = 2 * (1 + v ^ 2 / 2) := by ring
  have h1 : Real.sqrt (2 + v ^ 2) = Real.sqrt 2 * Real.sqrt (1 + v ^ 2 / 2) := by
    rw [hsq, Real.sqrt_mul (by norm_num)]
  have h3 : Real.sqrt (1 + v ^ 2 / 2) = (1 + v ^ 2 / 2) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have h4 : (1 + v ^ 2 / 2) ^ (-1 / 2 : ℝ) = ((1 + v ^ 2 / 2) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hpos.le]
  rw [h1, h3, h4]
  have hne : (1 + v ^ 2 / 2) ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  have hne2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

theorem watsonPoly_schlafliCoeff (m : ℕ) (v : ℝ) :
    watsonPoly schlafliCoeff (m + 1) v
      = (Real.sqrt 2)⁻¹ * ((∑ k ∈ Finset.range (m + 1), binomCoeff (-1 / 2 : ℝ) k * (v ^ 2) ^ k)
        + v ^ 2 * ∑ j ∈ Finset.range m, binomCoeff (-1 / 2 : ℝ) j * (v ^ 2) ^ j) := by
  have hpow : ∀ k : ℕ, v ^ (2 * k) = (v ^ 2) ^ k := fun k => by rw [pow_mul]
  rw [watsonPoly]
  simp only [hpow, schlafliCoeff]
  have hexp : ∀ k ∈ Finset.range (m + 1),
      (Real.sqrt 2)⁻¹ * (binomCoeff (-1 / 2 : ℝ) k
          + (if k = 0 then 0 else binomCoeff (-1 / 2 : ℝ) (k - 1))) * (v ^ 2) ^ k
        = (Real.sqrt 2)⁻¹ * (binomCoeff (-1 / 2 : ℝ) k * (v ^ 2) ^ k)
          + (Real.sqrt 2)⁻¹ * ((if k = 0 then 0 else binomCoeff (-1 / 2 : ℝ) (k - 1))
              * (v ^ 2) ^ k) := by
    intro k _
    ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← mul_add]
  congr 1
  congr 1
  rw [Finset.sum_range_succ']
  have hzero : (if (0 : ℕ) = 0 then (0 : ℝ) else binomCoeff (-1 / 2 : ℝ) (0 - 1))
      * (v ^ 2) ^ (0 : ℕ) = 0 := by simp
  rw [hzero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hif : (if j + 1 = 0 then (0 : ℝ) else binomCoeff (-1 / 2 : ℝ) (j + 1 - 1))
      = binomCoeff (-1 / 2 : ℝ) j := by simp
  rw [hif, pow_succ]
  ring

/-- **The Schläfli profile has a Taylor expansion in `v²` with a uniform remainder on the whole
half line.**  This is the profile input of Watson's lemma. -/
theorem abs_besselLaplaceProfile_sub_watsonPoly_le (m : ℕ) (v : ℝ) :
    |_root_.HTGeometry.besselLaplaceProfile v - watsonPoly schlafliCoeff (m + 1) v|
      ≤ (3 * (Real.sqrt 2)⁻¹ / 2 ^ (m + 1)) * v ^ (2 * (m + 1)) := by
  have hs : (0 : ℝ) ≤ v ^ 2 := by positivity
  have hdiff : _root_.HTGeometry.besselLaplaceProfile v - watsonPoly schlafliCoeff (m + 1) v
      = (Real.sqrt 2)⁻¹ * (binomRem (-1 / 2 : ℝ) (m + 1) (v ^ 2)
        + v ^ 2 * binomRem (-1 / 2 : ℝ) m (v ^ 2)) := by
    rw [besselLaplaceProfile_eq_shifted, watsonPoly_schlafliCoeff, binomRem, binomRem]
    ring
  have hb1 := abs_binomRem_neg_half_le (m + 1) hs
  have hb2 := abs_binomRem_neg_half_le m hs
  have hcalc : (v ^ 2 / 2) ^ (m + 1) + v ^ 2 * (v ^ 2 / 2) ^ m
      = 3 * (v ^ 2) ^ (m + 1) / 2 ^ (m + 1) := by
    rw [div_pow, div_pow, pow_succ]
    field_simp
    ring
  have hbound : |binomRem (-1 / 2 : ℝ) (m + 1) (v ^ 2)
      + v ^ 2 * binomRem (-1 / 2 : ℝ) m (v ^ 2)| ≤ 3 * (v ^ 2) ^ (m + 1) / 2 ^ (m + 1) := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_of_nonneg hs]
    have h2 : v ^ 2 * |binomRem (-1 / 2 : ℝ) m (v ^ 2)| ≤ v ^ 2 * (v ^ 2 / 2) ^ m :=
      mul_le_mul_of_nonneg_left hb2 hs
    linarith
  rw [hdiff, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹)]
  have hvp : v ^ (2 * (m + 1)) = (v ^ 2) ^ (m + 1) := by rw [pow_mul]
  rw [hvp]
  calc (Real.sqrt 2)⁻¹ * |binomRem (-1 / 2 : ℝ) (m + 1) (v ^ 2)
        + v ^ 2 * binomRem (-1 / 2 : ℝ) m (v ^ 2)|
      ≤ (Real.sqrt 2)⁻¹ * (3 * (v ^ 2) ^ (m + 1) / 2 ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 3 * (Real.sqrt 2)⁻¹ / 2 ^ (m + 1) * (v ^ 2) ^ (m + 1) := by ring

end SchlafliProfile

end

end GaloisForLFunctions.HTGeometry
