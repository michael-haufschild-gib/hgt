import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PortAdmissionCapacity

/-!
# The prime Gamma–Rees event germ and its cofinal nonuniformity

At a prime `p` the signed reflected Gamma determinant transgression and the clock-normalized
Rees–corona weight are two coordinates on the same real grade line.  Their quotient extends to the
entire even positive function

`g_p(t) = L_p · sinh(t log p)/(t log p)`,  `L_p = 4p³(log p)²/((p+1)²(p-1)(2p-1))`,

so `β_p = -g_p · w_p`: the two coordinates cut out the same simple zero at `t = 0` with opposite
raw coorientation, and after removing the reflection-odd sign they agree through a positive factor.
The removable value at the event is `L_p`, not `1`, and `L_p ~ 2(log p)²/p → 0`, so the primewise
comparisons do not assemble into a boundedly invertible unweighted diagonal chart.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open Filter Topology

section Sinhc

/-- The entire even extension of `sinh x / x`. -/
noncomputable def sinhc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sinh x / x

@[simp] theorem sinhc_zero : sinhc 0 = 1 := by simp [sinhc]

theorem sinhc_mul (x : ℝ) : sinhc x * x = Real.sinh x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sinhc, if_neg hx, div_mul_cancel₀ _ hx]

theorem sinhc_pos (x : ℝ) : 0 < sinhc x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [sinhc, if_neg hx.ne]
    have hs : Real.sinh x < 0 := by
      have := Real.sinh_strictMono hx
      simpa using this
    exact div_pos_of_neg_of_neg hs hx
  · simp
  · rw [sinhc, if_neg hx.ne']
    have hs : 0 < Real.sinh x := by
      have := Real.sinh_strictMono hx
      simpa using this
    exact div_pos hs hx

end Sinhc

section EventGerm

variable {p : ℕ}

/-- **`(GBR.1)`.**  The source-selected occupancy Fisher density. -/
noncomputable def fisherDensity (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) + 1) ^ 2

/-- **`(GBR.2)`.**  The signed reflected Gamma determinant transgression. -/
noncomputable def gammaTransgression (p : ℕ) (t : ℝ) : ℝ :=
  fisherDensity p * ((p : ℝ) ^ (-t) - (p : ℝ) ^ t)

/-- **`(GBR.5)`.**  The scalar weight of the clock-normalized Rees–corona quotient. -/
noncomputable def reesSlope (p : ℕ) : ℝ :=
  (1 - (p : ℝ)⁻¹) * (2 - (p : ℝ)⁻¹) / (2 * Real.log p)

noncomputable def reesWeight (p : ℕ) (t : ℝ) : ℝ := reesSlope p * t

/-- **`(GBR.6)`.**  The comparison constant. -/
noncomputable def eventConstant (p : ℕ) : ℝ :=
  4 * (p : ℝ) ^ 3 * Real.log p ^ 2 / (((p : ℝ) + 1) ^ 2 * ((p : ℝ) - 1) * (2 * (p : ℝ) - 1))

/-- **`(GBR.7)`.**  The entire even comparison function. -/
noncomputable def eventGerm (p : ℕ) (t : ℝ) : ℝ :=
  eventConstant p * sinhc (t * Real.log p)

@[simp] theorem eventGerm_zero (p : ℕ) : eventGerm p 0 = eventConstant p := by
  simp [eventGerm]

theorem eventGerm_pos (hp : 2 ≤ p) (t : ℝ) : 0 < eventGerm p t := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hpos : 0 < eventConstant p := by
    rw [eventConstant]
    have h1 : (0 : ℝ) < (p : ℝ) := by linarith
    have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h3 : (0 : ℝ) < 2 * (p : ℝ) - 1 := by linarith
    positivity
  exact mul_pos hpos (sinhc_pos _)

theorem rpow_sub_rpow_eq_sinh (hp : 2 ≤ p) (t : ℝ) :
    ((p : ℝ) ^ (-t) - (p : ℝ) ^ t) = -2 * Real.sinh (t * Real.log p) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
    linarith
  rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0, Real.sinh_eq]
  have h1 : Real.log p * -t = -(t * Real.log p) := by ring
  have h2 : Real.log p * t = t * Real.log p := by ring
  rw [h1, h2]
  ring

/-- The comparison constant is the exact ratio of the two coordinate slopes. -/
theorem eventConstant_mul_reesSlope (hp : 2 ≤ p) :
    eventConstant p * reesSlope p = 2 * fisherDensity p * Real.log p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  have hp0 : ((p : ℝ)) ≠ 0 := by linarith
  have h2 : ((p : ℝ) + 1) ≠ 0 := by linarith
  have h3 : ((p : ℝ) - 1) ≠ 0 := by linarith
  have h4 : (2 * (p : ℝ) - 1) ≠ 0 := by linarith
  have h4' : (-1 + (p : ℝ) * 2) ≠ 0 := by
    have : (0 : ℝ) < -1 + (p : ℝ) * 2 := by linarith
    exact this.ne'
  have hmul : (-1 + (p : ℝ) * 2) * (-1 + (p : ℝ) * 2)⁻¹ = 1 := mul_inv_cancel₀ h4'
  rw [eventConstant, reesSlope, fisherDensity]
  field_simp
  linear_combination 4 * hmul

/-- **Theorem 3.1, `(GBR.8)`.**  The Gamma determinant transgression is the negative of the
positive event germ times the Rees weight. -/
theorem gammaTransgression_eq (hp : 2 ≤ p) (t : ℝ) :
    gammaTransgression p t = -(eventGerm p t) * reesWeight p t := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  have hkey := eventConstant_mul_reesSlope hp
  have hsinh := sinhc_mul (t * Real.log p)
  rw [gammaTransgression, rpow_sub_rpow_eq_sinh hp, eventGerm, reesWeight]
  have hrw : -(eventConstant p * sinhc (t * Real.log p)) * (reesSlope p * t) * Real.log p
      = -(eventConstant p * reesSlope p) * (sinhc (t * Real.log p) * (t * Real.log p)) := by
    ring
  have hgoal : fisherDensity p * (-2 * Real.sinh (t * Real.log p)) * Real.log p
      = -(eventConstant p * sinhc (t * Real.log p)) * (reesSlope p * t) * Real.log p := by
    rw [hrw, hsinh, hkey]
    ring
  exact mul_right_cancel₀ hlog hgoal

/-- **Corollary 3.2, `(GBR.9)`.**  The two coordinates have the same simple zero at the event, and
their transverse derivatives are identified by the comparison constant. -/
theorem event_derivative (hp : 2 ≤ p) :
    HasDerivAt (gammaTransgression p) (-(2 * fisherDensity p * Real.log p)) 0 ∧
    HasDerivAt (reesWeight p) (reesSlope p) 0 ∧
    -(2 * fisherDensity p * Real.log p) = -(eventConstant p * reesSlope p) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
    linarith
  refine ⟨?_, ?_, by rw [eventConstant_mul_reesSlope hp]⟩
  · have hbase : HasDerivAt (fun t : ℝ => t * Real.log p) (1 * Real.log p) 0 :=
      (hasDerivAt_id (0 : ℝ)).mul_const (Real.log p)
    have hsinh := hbase.sinh
    have h2 := (hsinh.const_mul (-2 : ℝ)).const_mul (fisherDensity p)
    have hval : fisherDensity p * (-2 * (Real.cosh (0 * Real.log p) * (1 * Real.log p)))
        = -(2 * fisherDensity p * Real.log p) := by
      simp only [zero_mul, Real.cosh_zero, one_mul]
      ring
    rw [hval] at h2
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with t
    rw [gammaTransgression, rpow_sub_rpow_eq_sinh hp]
  · have h : HasDerivAt (reesWeight p) (reesSlope p * 1) 0 :=
      (hasDerivAt_id (0 : ℝ)).const_mul (reesSlope p)
    rwa [mul_one] at h

/-- **Proposition 4.1, `(GBR.10)`.**  At `p = 2` the removable event value is strictly below
`2/3`, hence different from `1`: the piecewise normalization that assigns the value `1` at the
event is discontinuous there. -/
theorem eventConstant_two_lt : eventConstant 2 < 2 / 3 ∧ eventConstant 2 ≠ 1 := by
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hval : eventConstant 2 = 32 * Real.log 2 ^ 2 / 27 := by
    rw [eventConstant]
    norm_num
  have hlt : eventConstant 2 < 2 / 3 := by
    rw [hval]
    nlinarith
  exact ⟨hlt, by intro h; rw [h] at hlt; norm_num at hlt⟩

end EventGerm

section CofinalNonuniformity

/-- The elementary bound `log n ≤ 2√n`. -/
theorem log_le_two_sqrt {n : ℕ} (hn : 1 ≤ n) : Real.log n ≤ 2 * Real.sqrt n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have h1 : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log n = 2 * Real.log (Real.sqrt n) := by
    rw [Real.log_sqrt hn0.le]
    ring
  rw [h2]
  linarith

theorem log_sq_le (n : ℕ) (hn : 1 ≤ n) : Real.log n ^ 2 ≤ 4 * (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h := log_le_two_sqrt hn
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

/-- **The comparison constants are uniformly bounded.** -/
theorem eventConstant_le_32 {n : ℕ} (hn : 2 ≤ n) : eventConstant n ≤ 32 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlogsq := log_sq_le n (by omega)
  have hden : ((n : ℝ) ^ 4) / 2 ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
    nlinarith [sq_nonneg ((n : ℝ) - 2), sq_nonneg ((n : ℝ)), pow_pos hn0 3, pow_pos hn0 4]
  have hdenpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
    have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
    positivity
  rw [eventConstant, div_le_iff₀ hdenpos]
  nlinarith [pow_pos hn0 3, pow_pos hn0 4]

theorem eventConstant_pos {n : ℕ} (hn : 2 ≤ n) : 0 < eventConstant n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  rw [eventConstant]
  positivity

/-- **Theorem 5.1, `(GBR.11)`.**  The comparison constants tend to zero across primes. -/
theorem tendsto_eventConstant_zero :
    Filter.Tendsto (fun n : ℕ => eventConstant n) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun n : ℕ => 8 * (Real.log n ^ 2 / (1 * (n : ℝ) + 0)))
      Filter.atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using h.const_mul (8 : ℝ)
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_ hlim
  · rcases le_or_gt 2 n with hn | hn
    · exact (eventConstant_pos hn).le
    · rw [eventConstant]
      interval_cases n <;> norm_num
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hden : ((n : ℝ) ^ 4) / 2 ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
      nlinarith [sq_nonneg ((n : ℝ) - 2), pow_pos hn0 3, pow_pos hn0 4]
    have hdenpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) := by
      have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
      positivity
    rw [eventConstant, div_le_iff₀ hdenpos]
    simp only [one_mul, add_zero]
    have hexp : 8 * (Real.log n ^ 2 / (n : ℝ)) *
        (((n : ℝ) + 1) ^ 2 * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1))
        = 8 * Real.log n ^ 2 *
          ((((n : ℝ) + 1) ^ 2 * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) / (n : ℝ)) := by
      field_simp
      try ring
    rw [hexp]
    have hge : ((n : ℝ) ^ 3) / 2
        ≤ (((n : ℝ) + 1) ^ 2 * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1)) / (n : ℝ) := by
      rw [le_div_iff₀ hn0]
      nlinarith [pow_pos hn0 3]
    nlinarith [pow_pos hn0 3, sq_nonneg (Real.log n)]

end CofinalNonuniformity

section DiagonalComparison

/-- The diagonal comparison coefficient at a prime. -/
noncomputable def diagCoef (p : Nat.Primes) : ℂ := (eventConstant (p : ℕ) : ℂ)

@[simp] theorem norm_diagCoef (p : Nat.Primes) : ‖diagCoef p‖ = eventConstant (p : ℕ) := by
  rw [diagCoef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eventConstant_pos p.2.two_le)]

theorem diagCoef_ne_zero (p : Nat.Primes) : diagCoef p ≠ 0 := by
  intro h
  have := norm_diagCoef p
  rw [h, norm_zero] at this
  exact (eventConstant_pos p.2.two_le).ne this

theorem norm_diagCoef_le (p : Nat.Primes) : ‖diagCoef p‖ ≤ 32 := by
  rw [norm_diagCoef]
  exact eventConstant_le_32 p.2.two_le

theorem memℓp_diagMul (x : SourceL2 Nat.Primes) :
    Memℓp (fun p => diagCoef p * (x : Nat.Primes → ℂ) p) 2 := by
  refine memℓp_two_iff.2 ?_
  refine ((memℓp_two_iff.1 x.2).mul_left ((32 : ℝ) ^ 2)).of_nonneg_of_le
    (fun p => by positivity) fun p => ?_
  rw [norm_mul, mul_pow]
  have h1 : ‖diagCoef p‖ ^ 2 ≤ (32 : ℝ) ^ 2 := by
    have := norm_diagCoef_le p
    nlinarith [norm_nonneg (diagCoef p)]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

theorem norm_diagMul_le (x : SourceL2 Nat.Primes) :
    ‖(⟨fun p => diagCoef p * (x : Nat.Primes → ℂ) p, memℓp_diagMul x⟩ : SourceL2 Nat.Primes)‖
      ≤ 32 * ‖x‖ := by
  set y : SourceL2 Nat.Primes :=
    ⟨fun p => diagCoef p * (x : Nat.Primes → ℂ) p, memℓp_diagMul x⟩ with hy
  have hcoord : ∀ p : Nat.Primes,
      ‖(y : Nat.Primes → ℂ) p‖ ^ 2 ≤ (32 : ℝ) ^ 2 * ‖(x : Nat.Primes → ℂ) p‖ ^ 2 := by
    intro p
    have hval : (y : Nat.Primes → ℂ) p = diagCoef p * (x : Nat.Primes → ℂ) p := rfl
    rw [hval, norm_mul, mul_pow]
    have h1 : ‖diagCoef p‖ ^ 2 ≤ (32 : ℝ) ^ 2 := by
      have := norm_diagCoef_le p
      nlinarith [norm_nonneg (diagCoef p)]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hsum : Summable fun p : Nat.Primes => (32 : ℝ) ^ 2 * ‖(x : Nat.Primes → ℂ) p‖ ^ 2 :=
    (memℓp_two_iff.1 x.2).mul_left _
  have hsq : ‖y‖ ^ 2 ≤ (32 : ℝ) ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    calc ∑' p : Nat.Primes, ‖(y : Nat.Primes → ℂ) p‖ ^ 2
        ≤ ∑' p : Nat.Primes, (32 : ℝ) ^ 2 * ‖(x : Nat.Primes → ℂ) p‖ ^ 2 :=
          (memℓp_two_iff.1 y.2).tsum_le_tsum hcoord hsum
      _ = (32 : ℝ) ^ 2 * ∑' p : Nat.Primes, ‖(x : Nat.Primes → ℂ) p‖ ^ 2 := tsum_mul_left
  nlinarith [norm_nonneg y, norm_nonneg x]

/-- **`(GBR.12)`.**  The diagonal comparison map on the prime source chart. -/
noncomputable def diagCompare : SourceL2 Nat.Primes →L[ℂ] SourceL2 Nat.Primes :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun p => diagCoef p * (x : Nat.Primes → ℂ) p, memℓp_diagMul x⟩
      map_add' := fun x y => by
        refine lp.ext (funext fun p => ?_)
        simp only [lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := fun a x => by
        refine lp.ext (funext fun p => ?_)
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring } 32 norm_diagMul_le

@[simp] theorem diagCompare_apply (x : SourceL2 Nat.Primes) (p : Nat.Primes) :
    (diagCompare x : Nat.Primes → ℂ) p = diagCoef p * (x : Nat.Primes → ℂ) p := rfl

theorem diagCompare_injective : Function.Injective diagCompare := by
  intro x y hxy
  refine lp.ext (funext fun p => ?_)
  have := congrArg (fun z : SourceL2 Nat.Primes => (z : Nat.Primes → ℂ) p) hxy
  simp only [diagCompare_apply] at this
  exact mul_left_cancel₀ (diagCoef_ne_zero p) this

theorem norm_diagCompare_srcBasis (p : Nat.Primes) :
    ‖diagCompare (srcBasis p)‖ = eventConstant (p : ℕ) := by
  have hval : diagCompare (srcBasis p) = lp.single 2 p (diagCoef p) := by
    refine lp.ext (funext fun q => ?_)
    rw [diagCompare_apply, lp.single_apply, srcBasis_apply]
    by_cases h : q = p
    · subst h; simp
    · simp [h]
  rw [hval, lp.norm_single (by norm_num), norm_diagCoef]

theorem norm_srcBasis (p : Nat.Primes) : ‖(srcBasis p : SourceL2 Nat.Primes)‖ = 1 := by
  rw [srcBasis, lp.norm_single (by norm_num)]
  simp

/-- **Corollary 5.2.**  The diagonal comparison has no uniformly bounded inverse on its range. -/
theorem no_uniform_inverse_diagCompare :
    ¬ ∃ C : ℝ, ∀ x : SourceL2 Nat.Primes, ‖x‖ ≤ C * ‖diagCompare x‖ := by
  rintro ⟨C, hC⟩
  have hlim := tendsto_eventConstant_zero
  have hCpos : 0 < C := by
    have h2 : Nat.Primes := ⟨2, Nat.prime_two⟩
    have := hC (srcBasis h2)
    rw [norm_srcBasis, norm_diagCompare_srcBasis] at this
    nlinarith [eventConstant_pos h2.2.two_le, eventConstant_le_32 h2.2.two_le]
  have hev : ∀ᶠ n : ℕ in Filter.atTop, eventConstant n < C⁻¹ :=
    (tendsto_order.1 hlim).2 C⁻¹ (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨q, hqN, hqprime⟩ := Nat.exists_infinite_primes N
  set p : Nat.Primes := ⟨q, hqprime⟩ with hp
  have h1 := hC (srcBasis p)
  rw [norm_srcBasis, norm_diagCompare_srcBasis] at h1
  have h2 : eventConstant (p : ℕ) < C⁻¹ := hN q hqN
  have h3 : C * eventConstant (p : ℕ) < C * C⁻¹ := by
    exact mul_lt_mul_of_pos_left h2 hCpos
  rw [mul_inv_cancel₀ hCpos.ne'] at h3
  linarith

/-- **Corollary 5.2.**  Its range is not closed. -/
theorem range_diagCompare_not_closed :
    ¬ IsClosed ((LinearMap.range (diagCompare : SourceL2 Nat.Primes →ₗ[ℂ] SourceL2 Nat.Primes)) :
      Set (SourceL2 Nat.Primes)) := by
  intro hclosed
  set S : Submodule ℂ (SourceL2 Nat.Primes) :=
    LinearMap.range (diagCompare : SourceL2 Nat.Primes →ₗ[ℂ] SourceL2 Nat.Primes) with hS
  haveI : CompleteSpace S := hclosed.completeSpace_coe
  set f : SourceL2 Nat.Primes →L[ℂ] S := diagCompare.codRestrict S (fun x => ⟨x, rfl⟩) with hf
  have hinj : LinearMap.ker (f : SourceL2 Nat.Primes →ₗ[ℂ] S) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have : diagCompare x = 0 := by
      have := congrArg (Subtype.val) hx
      simpa [hf] using this
    have h0 : diagCompare x = diagCompare 0 := by rw [this, map_zero]
    exact diagCompare_injective h0
  have hsurj : LinearMap.range (f : SourceL2 Nat.Primes →ₗ[ℂ] S) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  set e := ContinuousLinearEquiv.ofBijective f hinj hsurj with he
  refine no_uniform_inverse_diagCompare ⟨‖(e.symm : S →L[ℂ] SourceL2 Nat.Primes)‖, fun x => ?_⟩
  have hx : x = e.symm (e x) := (e.symm_apply_apply x).symm
  have hb := (e.symm : S →L[ℂ] SourceL2 Nat.Primes).le_opNorm (e x)
  have hnorm : ‖(e x : S)‖ = ‖diagCompare x‖ := rfl
  calc ‖x‖ = ‖e.symm (e x)‖ := by rw [← hx]
    _ ≤ ‖(e.symm : S →L[ℂ] SourceL2 Nat.Primes)‖ * ‖e x‖ := hb
    _ = ‖(e.symm : S →L[ℂ] SourceL2 Nat.Primes)‖ * ‖diagCompare x‖ := by rw [hnorm]

end DiagonalComparison

end HTGeometry.ConstraintMotiveRelativity
