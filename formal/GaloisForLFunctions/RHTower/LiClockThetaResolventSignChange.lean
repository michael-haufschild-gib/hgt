import GaloisForLFunctions.RHTower.LiClockThetaMassiveForcing

/-!
# The theta resolvent changes sign

The literal kernels have every positive exponential type: for each `ε > 0`,
`|B^{(m)}(t)|, |K^{(m)}(t)| ≤ M_ε ε^m e^{ε|t|}` at every real clock, because the generator
coefficients satisfy `c_k ≤ e^{32/(303 ε²)} ε^{2k}`.  Hence `K` has a Laplace transform for every
`p > 0`, and termwise integration gives `K̂(p) = Φ(1/p) - 1`.

The resolvent `r = -u''` of `r + r ⋆ K = K` satisfies `r(0) = 0`, `r'(0) = ν₁/2 > 0`, so it is
positive on an initial interval `(0, ε]`.  If `r ≥ 0` on all nonnegative clocks, then `0 ≤ r ≤ K`,
so `r̂(p) = K̂/(1 + K̂)` for every `p > 0`; comparing `r̂(q/2) - r̂(q) ≤ q²/c₁` (from
`K̂(q) ≥ c₁/q²`) with `r̂(q/2) - r̂(q) ≥ (q/2) e^{-qε} ∫_0^ε t r(t) dt` and letting `q` be small
contradicts the positivity of `r` near the origin.  So `r` takes a negative value at a positive
clock, although `K` is odd entire with every odd Taylor coefficient strictly positive.

The same kernel also forces a negative value of the causal inverse `u` of `u + u ⋆ K = t`: a
nonnegative `u` with initial mass `m` would give `u ⋆ K ≥ m K(T) ≥ m c₂ T³/6` at the clock
`ε + T`, which outgrows `ε + T`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Every positive exponential type -/

theorem liClockThetaGeneratorCoeff_le_pow {R : ℝ} (hR : 0 < R) (k : ℕ) :
    liClockThetaGeneratorCoeff k ≤ Real.exp (32 / (303 * R ^ 2)) * R ^ (2 * k) := by
  have h1 := liClockThetaGeneratorCoeff_le k
  have h2 := Real.pow_div_factorial_le_exp (32 / (303 * R ^ 2)) (by positivity) k
  have e : (32 / 303 : ℝ) ^ k / (k.factorial : ℝ) =
      R ^ (2 * k) * ((32 / (303 * R ^ 2)) ^ k / (k.factorial : ℝ)) := by
    rw [pow_mul, ← mul_div_assoc, ← mul_pow]
    congr 2
    field_simp
  calc liClockThetaGeneratorCoeff k ≤ (32 / 303 : ℝ) ^ k / (k.factorial : ℝ) := h1
    _ = R ^ (2 * k) * ((32 / (303 * R ^ 2)) ^ k / (k.factorial : ℝ)) := e
    _ ≤ R ^ (2 * k) * Real.exp (32 / (303 * R ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := mul_comm _ _

theorem geometricCoeffBound_evenSpread_liClockThetaGeneratorCoeff {R : ℝ} (hR : 0 < R) :
    GeometricCoeffBound (evenSpread liClockThetaGeneratorCoeff)
      (Real.exp (32 / (303 * R ^ 2))) R := by
  intro N
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' N
  · rw [hk, evenSpread_two_mul, abs_of_pos (liClockThetaGeneratorCoeff_pos k)]
    exact liClockThetaGeneratorCoeff_le_pow hR k
  · rw [hk, evenSpread_two_mul_add_one, abs_zero]; positivity

theorem geometricCoeffBound_oddSpread_liClockThetaKernelCoeff {R : ℝ} (hR : 0 < R) :
    GeometricCoeffBound (oddSpread fun m => liClockThetaGeneratorCoeff (m + 1))
      (R * Real.exp (32 / (303 * R ^ 2))) R := by
  intro N
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' N
  · rw [hk, oddSpread_two_mul, abs_zero]; positivity
  · rw [hk, oddSpread_two_mul_add_one, abs_of_pos (liClockThetaGeneratorCoeff_pos _)]
    calc liClockThetaGeneratorCoeff (k + 1) ≤
        Real.exp (32 / (303 * R ^ 2)) * R ^ (2 * (k + 1)) := liClockThetaGeneratorCoeff_le_pow hR _
      _ = R * Real.exp (32 / (303 * R ^ 2)) * R ^ (2 * k + 1) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]; ring

theorem liEvenCrossActualClockBorelKernel_eq_borelSeries :
    liEvenCrossActualClockBorelKernel = borelSeries (evenSpread liClockThetaGeneratorCoeff) := by
  rw [funext liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries]
  exact evenFactorialSeries_eq_borelSeries (by norm_num) geometricCoeffBound_liClockThetaGeneratorCoeff

theorem liClockThetaKernel_eq_borelSeries :
    liClockThetaKernel = borelSeries (oddSpread fun m => liClockThetaGeneratorCoeff (m + 1)) := by
  funext t
  unfold liClockThetaKernel
  rw [oddFactorialSeries_eq_borelSeries (by norm_num)
    geometricCoeffBound_liClockThetaGeneratorCoeff.shift]

/-- **Every positive exponential type for `B`.**
`|B^{(m)}(t)| ≤ e^{32/(303ε²)} ε^m e^{ε|t|}` for every `ε > 0`, `m` and real `t`. -/
theorem abs_iteratedDeriv_liEvenCrossActualClockBorelKernel_le {ε : ℝ} (hε : 0 < ε) (m : ℕ)
    (t : ℝ) : |iteratedDeriv m liEvenCrossActualClockBorelKernel t| ≤
      Real.exp (32 / (303 * ε ^ 2)) * ε ^ m * Real.exp (ε * |t|) := by
  have hb := geometricCoeffBound_evenSpread_liClockThetaGeneratorCoeff hε
  rw [liEvenCrossActualClockBorelKernel_eq_borelSeries, iteratedDeriv_borelSeries hb]
  exact abs_borelSeries_le (geometricCoeffBound_shift_add hb m) t

/-- **Every positive exponential type for `K`.**
`|K^{(m)}(t)| ≤ ε e^{32/(303ε²)} ε^m e^{ε|t|}` for every `ε > 0`, `m` and real `t`. -/
theorem abs_iteratedDeriv_liClockThetaKernel_le {ε : ℝ} (hε : 0 < ε) (m : ℕ) (t : ℝ) :
    |iteratedDeriv m liClockThetaKernel t| ≤
      ε * Real.exp (32 / (303 * ε ^ 2)) * ε ^ m * Real.exp (ε * |t|) := by
  have hb := geometricCoeffBound_oddSpread_liClockThetaKernelCoeff hε
  rw [liClockThetaKernel_eq_borelSeries, iteratedDeriv_borelSeries hb]
  exact abs_borelSeries_le (geometricCoeffBound_shift_add hb m) t

/-! ## The Laplace transform of the kernel -/

theorem integrableOn_liClockThetaKernel_mul_exp_neg {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => liClockThetaKernel t * Real.exp (-(p * t))) (Ioi 0) := by
  rw [liClockThetaKernel_eq_borelSeries]
  exact integrableOn_borelSeries_mul_exp_neg
    (geometricCoeffBound_oddSpread_liClockThetaKernelCoeff (half_pos hp)) (by linarith)

/-- `K̂(p) = Σ_k c_{k+1} p^{-2k-2}` for every `p > 0`. -/
theorem hasSum_integral_Ioi_liClockThetaKernel_mul_exp_neg {p : ℝ} (hp : 0 < p) :
    HasSum (fun k : ℕ => liClockThetaGeneratorCoeff (k + 1) * (p ^ (2 * k + 2))⁻¹)
      (∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t))) := by
  have h := hasSum_integral_Ioi_borelSeries_mul_exp_neg
    (geometricCoeffBound_oddSpread_liClockThetaKernelCoeff (half_pos hp)) (by linarith)
    (by linarith : p / 2 < p)
  rw [← liClockThetaKernel_eq_borelSeries] at h
  set f : ℕ → ℝ := fun N => oddSpread (fun m => liClockThetaGeneratorCoeff (m + 1)) N *
    (p ^ (N + 1))⁻¹ with hfdef
  have hodd : Summable fun k : ℕ => f (2 * k + 1) :=
    h.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) fun x y hxy => by simpa using hxy
  have heven : HasSum (fun k : ℕ => f (2 * k)) 0 := by
    simp only [hfdef, oddSpread_two_mul, zero_mul]
    exact hasSum_zero
  have hall := heven.even_add_odd hodd.hasSum
  rw [zero_add] at hall
  rw [h.unique hall]
  refine hodd.hasSum.congr_fun fun k => ?_
  simp only [hfdef, oddSpread_two_mul_add_one]

/-- **Laplace transform of the kernel.**  `K̂(p) = Φ(1/p) - 1` for every `p > 0`. -/
theorem integral_Ioi_liClockThetaKernel_mul_exp_neg_eq {p : ℝ} (hp : 0 < p) :
    ((∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t)) : ℝ) : ℂ) =
      liClockThetaGenerator ((p : ℂ)⁻¹) - 1 := by
  have hL := hasSum_integral_Ioi_liClockThetaKernel_mul_exp_neg hp
  have hfull : HasSum (fun j : ℕ => liClockThetaGeneratorCoeff j * (p⁻¹) ^ (2 * j))
      ((∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t))) + 1) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, liClockThetaGeneratorCoeff_zero, mul_zero,
      pow_zero, mul_one, add_sub_cancel_right]
    refine hL.congr_fun fun k => ?_
    rw [inv_pow, show 2 * (k + 1) = 2 * k + 2 by ring]
  unfold liClockThetaGenerator
  have hc : ∀ j : ℕ, (liClockThetaGeneratorCoeff j : ℂ) * ((p : ℂ)⁻¹) ^ (2 * j) =
      ((liClockThetaGeneratorCoeff j * (p⁻¹) ^ (2 * j) : ℝ) : ℂ) := fun j => by push_cast; rfl
  simp_rw [hc]
  rw [← Complex.ofReal_tsum, hfull.tsum_eq]
  push_cast
  ring

theorem liClockThetaGeneratorCoeff_one_div_sq_le_integral {q : ℝ} (hq : 0 < q) :
    liClockThetaGeneratorCoeff 1 * (q ^ 2)⁻¹ ≤
      ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(q * t)) := by
  have h := le_hasSum (hasSum_integral_Ioi_liClockThetaKernel_mul_exp_neg hq) 0
    fun j _ => mul_nonneg (liClockThetaGeneratorCoeff_pos _).le (by positivity)
  simpa using h

/-! ## Positivity of the resolvent near the origin -/

theorem exists_liClockThetaResolvent_pos :
    ∃ ε > 0, ∀ t ∈ Ioc (0 : ℝ) ε, 0 < liClockThetaResolvent t := by
  have hν : 0 < thetaCuspNormalizedEvenMoment 1 / 2 := by
    have := thetaCuspNormalizedEvenMoment_pos 1; positivity
  have h := hasDerivAt_liClockThetaResolvent_zero.tendsto_slope_zero_right
  have hev := h.eventually_const_lt hν
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨u / 2, half_pos hu, fun t ht => ?_⟩
  have htu : t ∈ Ioo 0 u := ⟨ht.1, by linarith [ht.2, (show (0 : ℝ) < u from hu)]⟩
  have hs := hsub htu
  simp only [mem_setOf_eq, zero_add, liClockThetaResolvent_zero, sub_zero, smul_eq_mul] at hs
  have ht0 : 0 < t := ht.1
  have := mul_pos hs ht0
  rwa [inv_mul_eq_div, div_mul_cancel₀ _ ht0.ne'] at this

/-! ## The sign change -/

private theorem complex_integral_eq_ofReal (p : ℝ) (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * f t : ℝ) : ℂ) := by
  have h1 : ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-(p * t)) * f t : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by push_cast; ring_nf
  rw [h1]
  exact integral_ofReal

private theorem resolvent_le_kernel (hr : ∀ t, 0 ≤ t → 0 ≤ liClockThetaResolvent t) {t : ℝ}
    (ht : 0 ≤ t) : liClockThetaResolvent t ≤ liClockThetaKernel t := by
  have h := liClockThetaResolvent_volterra t
  have hc : 0 ≤ volterraConv liClockThetaResolvent liClockThetaKernel t := by
    unfold volterraConv
    exact intervalIntegral.integral_nonneg ht fun s hs =>
      mul_nonneg (hr _ (by linarith [hs.2])) (liClockThetaKernel_nonneg hs.1)
  linarith

private theorem integrableOn_resolvent_mul_exp
    (hr : ∀ t, 0 ≤ t → 0 ≤ liClockThetaResolvent t) {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaResolvent t) (Ioi 0) := by
  refine ((integrableOn_liClockThetaKernel_mul_exp_neg hp)).mono'
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul
      continuous_liClockThetaResolvent).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hr t ht'), mul_comm]
  exact mul_le_mul_of_nonneg_right (resolvent_le_kernel hr ht') (Real.exp_pos _).le

/-- Under `r ≥ 0`, `r̂(p) (1 + K̂(p)) = K̂(p)` for every `p > 0`. -/
private theorem laplace_resolvent_mul (hr : ∀ t, 0 ≤ t → 0 ≤ liClockThetaResolvent t)
    {p : ℝ} (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolvent t) *
        (1 + ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernel t) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernel t := by
  have hKi : IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaKernel t) (Ioi 0) :=
    (integrableOn_liClockThetaKernel_mul_exp_neg hp).congr_fun
      (fun t _ => mul_comm _ _) measurableSet_Ioi
  have hri := integrableOn_resolvent_mul_exp hr hp
  have hfi : IntegrableOn (fun t => Real.exp (-((p : ℂ).re * t)) * |liClockThetaResolvent t|)
      (Ioi 0) := by
    refine hri.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Complex.ofReal_re]
    rw [abs_of_nonneg (hr t (le_of_lt ht))]
  have hgi : IntegrableOn (fun t => Real.exp (-((p : ℂ).re * t)) * |liClockThetaKernel t|)
      (Ioi 0) := by
    refine hKi.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Complex.ofReal_re]
    rw [abs_of_nonneg (liClockThetaKernel_nonneg (le_of_lt ht))]
  have hconv := integral_Ioi_cexp_mul_volterraConv continuous_liClockThetaResolvent
    continuous_liClockThetaKernel hfi hgi
  rw [complex_integral_eq_ofReal, complex_integral_eq_ofReal, complex_integral_eq_ofReal,
    ← Complex.ofReal_mul] at hconv
  have hreal := Complex.ofReal_injective hconv
  have hsub : (fun t => Real.exp (-(p * t)) *
      volterraConv liClockThetaResolvent liClockThetaKernel t) =
      fun t => Real.exp (-(p * t)) * liClockThetaKernel t -
        Real.exp (-(p * t)) * liClockThetaResolvent t := by
    funext t
    have := liClockThetaResolvent_volterra t
    rw [show volterraConv liClockThetaResolvent liClockThetaKernel t =
      liClockThetaKernel t - liClockThetaResolvent t by linarith]
    ring
  rw [hsub, integral_sub hKi hri] at hreal
  linarith

theorem liClockThetaGeneratorCoeff_one_pos : 0 < liClockThetaGeneratorCoeff 1 :=
  liClockThetaGeneratorCoeff_pos 1

/-- **Sign change of the resolvent.**  The genuine resolvent of `r + r ⋆ K = K` takes a negative
value at a positive clock. -/
theorem exists_liClockThetaResolvent_neg : ∃ t > 0, liClockThetaResolvent t < 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hr : ∀ t, 0 ≤ t → 0 ≤ liClockThetaResolvent t := fun t ht => by
    rcases ht.eq_or_lt with h | h
    · rw [← h, liClockThetaResolvent_zero]
    · exact hcon t h
  obtain ⟨ε, hε, hpos⟩ := exists_liClockThetaResolvent_pos
  have hcont : Continuous fun t => t * liClockThetaResolvent t :=
    continuous_id.mul continuous_liClockThetaResolvent
  set J := ∫ t in (0 : ℝ)..ε, t * liClockThetaResolvent t with hJdef
  have hJ : 0 < J := intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
    (fun x hx => mul_pos hx.1 (hpos x ⟨hx.1, hx.2.le⟩)) hε
  set c1 := liClockThetaGeneratorCoeff 1
  have hc1 : 0 < c1 := liClockThetaGeneratorCoeff_one_pos
  set L : ℝ → ℝ := fun p => ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaResolvent t
  set LK : ℝ → ℝ := fun p => ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernel t
  have hLK : ∀ q, 0 < q → c1 * (q ^ 2)⁻¹ ≤ LK q := fun q hq => by
    have := liClockThetaGeneratorCoeff_one_div_sq_le_integral hq
    simp only [LK]
    rwa [show (fun t => Real.exp (-(q * t)) * liClockThetaKernel t) =
      fun t => liClockThetaKernel t * Real.exp (-(q * t)) from funext fun t => mul_comm _ _]
  -- upper bound of the difference quotient
  have hupper : ∀ q, 0 < q → L (q / 2) - L q ≤ q ^ 2 / c1 := by
    intro q hq
    have h1 := laplace_resolvent_mul hr (half_pos hq)
    have h2 := laplace_resolvent_mul hr hq
    have hK1 : 0 ≤ LK (q / 2) := (mul_nonneg hc1.le (by positivity)).trans (hLK _ (half_pos hq))
    have hK2 := hLK q hq
    have hK2' : 0 < LK q := lt_of_lt_of_le (by positivity) hK2
    have hLp : L (q / 2) ≤ 1 := by
      have : L (q / 2) * (1 + LK (q / 2)) ≤ 1 * (1 + LK (q / 2)) := by
        simp only [L, LK] at h1 ⊢; rw [h1]; linarith
      exact le_of_mul_le_mul_right this (by linarith)
    have hLq : 1 - L q = 1 / (1 + LK q) := by
      field_simp
      simp only [L, LK] at h2 ⊢
      linarith
    have hfrac : 1 / (1 + LK q) ≤ q ^ 2 / c1 := by
      rw [div_le_div_iff₀ (by linarith) hc1, one_mul]
      have : c1 ≤ LK q * q ^ 2 := by
        have := mul_le_mul_of_nonneg_right hK2 (by positivity : (0 : ℝ) ≤ q ^ 2)
        rwa [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one] at this
      nlinarith
    linarith
  -- lower bound of the difference quotient
  have hlower : ∀ q, 0 < q → q / 2 * Real.exp (-(q * ε)) * J ≤ L (q / 2) - L q := by
    intro q hq
    have hp := half_pos hq
    have hi1 := integrableOn_resolvent_mul_exp hr hp
    have hi2 := integrableOn_resolvent_mul_exp hr hq
    have hdiff : L (q / 2) - L q = ∫ t in Ioi (0 : ℝ),
        (Real.exp (-(q / 2 * t)) - Real.exp (-(q * t))) * liClockThetaResolvent t := by
      simp only [L]
      rw [← integral_sub hi1 hi2]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    have hint : IntegrableOn (fun t => (Real.exp (-(q / 2 * t)) - Real.exp (-(q * t))) *
        liClockThetaResolvent t) (Ioi 0) :=
      (hi1.sub hi2).congr_fun (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
    have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ (Real.exp (-(q / 2 * t)) - Real.exp (-(q * t))) *
        liClockThetaResolvent t := fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      refine mul_nonneg ?_ (hr t ht'.le)
      have : Real.exp (-(q * t)) ≤ Real.exp (-(q / 2 * t)) := Real.exp_le_exp.2 (by nlinarith)
      linarith
    have hmono := setIntegral_mono_set (s := Ioc (0 : ℝ) ε) (t := Ioi 0) hint
      (ae_restrict_of_forall_mem measurableSet_Ioi hnn)
      (Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)
    have hpt : ∀ t ∈ Ioc (0 : ℝ) ε, q / 2 * Real.exp (-(q * ε)) * (t * liClockThetaResolvent t) ≤
        (Real.exp (-(q / 2 * t)) - Real.exp (-(q * t))) * liClockThetaResolvent t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have hrt := (hpos t ht).le
      have hgap : q / 2 * t * Real.exp (-(q * t)) ≤
          Real.exp (-(q / 2 * t)) - Real.exp (-(q * t)) := by
        have h := Real.add_one_le_exp (q / 2 * t)
        have e : Real.exp (-(q / 2 * t)) = Real.exp (q / 2 * t) * Real.exp (-(q * t)) := by
          rw [← Real.exp_add]; ring_nf
        rw [e]
        nlinarith [Real.exp_pos (-(q * t))]
      have hexp : Real.exp (-(q * ε)) ≤ Real.exp (-(q * t)) :=
        Real.exp_le_exp.2 (by nlinarith [ht.2])
      have := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ q / 2 * t)
      calc q / 2 * Real.exp (-(q * ε)) * (t * liClockThetaResolvent t) =
          (q / 2 * t * Real.exp (-(q * ε))) * liClockThetaResolvent t := by ring
        _ ≤ (q / 2 * t * Real.exp (-(q * t))) * liClockThetaResolvent t :=
            mul_le_mul_of_nonneg_right (by nlinarith) hrt
        _ ≤ _ := mul_le_mul_of_nonneg_right hgap hrt
    have hmono2 := setIntegral_mono_on
      ((hcont.const_mul (q / 2 * Real.exp (-(q * ε)))).integrableOn_Ioc)
      (hint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hpt
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hε.le] at hmono2
    rw [hdiff]
    linarith
  -- choose a small clock frequency
  set E := Real.exp (-ε)
  have hE : 0 < E := Real.exp_pos _
  set q := min 1 (J * c1 * E / 4)
  have hq : 0 < q := lt_min one_pos (by positivity)
  have hq1 : q ≤ 1 := min_le_left _ _
  have hq2 : q ≤ J * c1 * E / 4 := min_le_right _ _
  have hEq : E ≤ Real.exp (-(q * ε)) := Real.exp_le_exp.2 (by nlinarith)
  have hlo := hlower q hq
  have hup := hupper q hq
  have h1 : q / 2 * E * J ≤ q ^ 2 / c1 := by
    have := mul_le_mul_of_nonneg_left hEq (by positivity : (0 : ℝ) ≤ q / 2)
    nlinarith [mul_le_mul_of_nonneg_right this hJ.le]
  have h2 : q ^ 2 / c1 ≤ q * (J * E / 4) := by
    rw [div_le_iff₀ hc1]
    nlinarith
  nlinarith [mul_pos (mul_pos hq hE) hJ]

/-! ## The causal inverse also changes sign -/

theorem liClockThetaKernelDeriv_nonneg (t : ℝ) : 0 ≤ liClockThetaKernelDeriv t := by
  unfold liClockThetaKernelDeriv evenFactorialSeries
  refine tsum_nonneg fun j => ?_
  have := (liClockThetaGeneratorCoeff_pos (j + 1)).le
  rw [pow_mul]; positivity

theorem monotone_liClockThetaKernel : Monotone liClockThetaKernel :=
  monotone_of_deriv_nonneg (fun t => (hasDerivAt_liClockThetaKernel t).differentiableAt)
    fun t => by rw [(hasDerivAt_liClockThetaKernel t).deriv]; exact liClockThetaKernelDeriv_nonneg t

/-- The cubic floor `K(v) ≥ ν₂ v³/144` on nonnegative clocks. -/
theorem liClockThetaKernel_ge_cubic {v : ℝ} (hv : 0 ≤ v) :
    liClockThetaGeneratorCoeff 2 * v ^ 3 / 6 ≤ liClockThetaKernel v := by
  have hb : GeometricCoeffBound (fun m => if m = 1 then liClockThetaGeneratorCoeff 2 else 0)
      (liClockThetaGeneratorCoeff 2) 1 := fun m => by
    dsimp only
    split_ifs <;> simp [abs_of_pos (liClockThetaGeneratorCoeff_pos 2),
      (liClockThetaGeneratorCoeff_pos 2).le]
  have h := oddFactorialSeries_le_of_le (by norm_num) (by norm_num) hb
    geometricCoeffBound_liClockThetaGeneratorCoeff.shift (fun m => by
      split_ifs with hm
      · rw [hm]
      · exact (liClockThetaGeneratorCoeff_pos _).le) hv
  have e : oddFactorialSeries (fun m => if m = 1 then liClockThetaGeneratorCoeff 2 else 0) v =
      liClockThetaGeneratorCoeff 2 * v ^ 3 / 6 := by
    unfold oddFactorialSeries
    rw [tsum_eq_single 1]
    · simp [Nat.factorial]
    · intro j hj; simp [hj]
  rw [e] at h
  exact h

theorem liClockThetaGeneratorCoeff_two :
    liClockThetaGeneratorCoeff 2 = thetaCuspNormalizedEvenMoment 2 / 24 := by
  simp [liClockThetaGeneratorCoeff, Nat.factorial]

/-- **Sign change of the causal inverse.**  The entire odd solution of `u + u ⋆ K = t` takes a
negative value at a positive clock. -/
theorem exists_liClockThetaCausalInverse_neg : ∃ t > 0, liClockThetaCausalInverse t < 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hjets := liClockThetaCausalInverse_initial_jets
  have hu0 : liClockThetaCausalInverse 0 = 0 := by simpa using hjets.1
  have hu : ∀ t, 0 ≤ t → 0 ≤ liClockThetaCausalInverse t := fun t ht => by
    rcases ht.eq_or_lt with h | h
    · rw [← h, hu0]
    · exact hcon t h
  have hdiff : Differentiable ℝ liClockThetaCausalInverse := by
    rw [liClockThetaCausalInverse_eq_borelSeries]
    exact fun t => (hasDerivAt_borelSeries geometricCoeffBound_liClockThetaInverseBorelCoeff
      t).differentiableAt
  have hcontu : Continuous liClockThetaCausalInverse := hdiff.continuous
  have hd1 : HasDerivAt liClockThetaCausalInverse 1 0 := by
    have h := (hdiff 0).hasDerivAt
    rwa [← iteratedDeriv_one, hjets.2.1] at h
  -- positivity on an initial interval
  obtain ⟨ε, hε, hpos⟩ : ∃ ε > 0, ∀ t ∈ Ioc (0 : ℝ) ε, 0 < liClockThetaCausalInverse t := by
    have hev := hd1.tendsto_slope_zero_right.eventually_const_lt one_pos
    obtain ⟨w, hw, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    refine ⟨w / 2, half_pos hw, fun t ht => ?_⟩
    have htw : t ∈ Ioo 0 w := ⟨ht.1, by linarith [ht.2, (show (0 : ℝ) < w from hw)]⟩
    have hs := hsub htw
    simp only [mem_setOf_eq, zero_add, hu0, sub_zero, smul_eq_mul] at hs
    have ht0 : 0 < t := ht.1
    have := mul_pos hs ht0
    rwa [inv_mul_eq_div, div_mul_cancel₀ _ ht0.ne'] at this
  set m := ∫ s in (0 : ℝ)..ε, liClockThetaCausalInverse s
  have hm : 0 < m := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hcontu.intervalIntegrable _ _) (fun x hx => hpos x ⟨hx.1, hx.2.le⟩) hε
  set c2 := liClockThetaGeneratorCoeff 2
  have hc2 : 0 < c2 := liClockThetaGeneratorCoeff_pos 2
  set A := c2 * m / 6
  have hA : 0 < A := by positivity
  set T := (ε + 1) / A + 1
  have hT1 : 1 ≤ T := by have : 0 ≤ (ε + 1) / A := by positivity
                         linarith
  have hT : (ε + 1) / A < T := by linarith
  -- the convolution lower bound at the clock `ε + T`
  set t := ε + T
  have hconv : A * T ^ 3 ≤ volterraConv liClockThetaCausalInverse liClockThetaKernel t := by
    rw [volterraConv_comm]
    unfold volterraConv
    have hcK : Continuous fun s => liClockThetaKernel (t - s) * liClockThetaCausalInverse s :=
      (continuous_liClockThetaKernel.comp (continuous_const.sub continuous_id)).mul hcontu
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hcK.intervalIntegrable (μ := volume) 0 ε) (hcK.intervalIntegrable (μ := volume) ε t)
    have htail : 0 ≤ ∫ s in ε..t, liClockThetaKernel (t - s) * liClockThetaCausalInverse s :=
      intervalIntegral.integral_nonneg (by linarith) fun s hs =>
        mul_nonneg (liClockThetaKernel_nonneg (by linarith [hs.2]))
          (hu s (by linarith [hs.1]))
    have hhead : liClockThetaKernel T * m ≤
        ∫ s in (0 : ℝ)..ε, liClockThetaKernel (t - s) * liClockThetaCausalInverse s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hε.le
        ((hcontu.const_mul _).intervalIntegrable _ _) (hcK.intervalIntegrable _ _) fun s hs => ?_
      exact mul_le_mul_of_nonneg_right (monotone_liClockThetaKernel (by linarith [hs.2]))
        (hu s hs.1)
    have hcub := liClockThetaKernel_ge_cubic (by linarith : (0 : ℝ) ≤ T)
    have hK : A * T ^ 3 ≤ liClockThetaKernel T * m := by
      have := mul_le_mul_of_nonneg_right hcub hm.le
      calc A * T ^ 3 = c2 * T ^ 3 / 6 * m := by ring
        _ ≤ _ := this
    linarith
  have hvol := liClockThetaCausalInverse_volterra t
  have hgrow : t < A * T ^ 3 := by
    have h1 : ε + 1 < A * T := by rwa [div_lt_iff₀ hA, mul_comm] at hT
    have h2 : T ≤ T ^ 2 := by nlinarith
    nlinarith
  have := hu t (by positivity)
  linarith

end RHTower
