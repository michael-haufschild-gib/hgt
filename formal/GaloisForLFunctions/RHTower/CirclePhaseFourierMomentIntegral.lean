import GaloisForLFunctions.RHTower.CircleHardyPhaseTraceIndex

/-!
# The signed first Fourier moment of a smooth circle phase is its winding integral

For a `1`-periodic `C²` function `f : ℝ → ℂ` of modulus one:

* `\hat{f'}(n) = 2πi n \hat f(n)` (integration by parts; the boundary term cancels by periodicity);
* Parseval gives `∫₀¹ \bar f f' = 2πi ∑_n n |\hat f(n)|²`;
* Parseval for `f''` gives `∑ n⁴ |\hat f(n)|² < ∞`, hence `∑ |n| |\hat f(n)| < ∞`.

So `f` defines a circle phase in the sense of `CircleHardyPhaseTraceIndex`, and the relative index
of the pair `(M_f† P M_f, P)` is the winding integral `(2πi)⁻¹ ∫₀¹ \bar f f'`.  Classical; no
novelty claim.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral
open scoped Real

namespace RHTower

/-- The circle function of a function on `ℝ`, read on the fundamental domain `[0, 1)`. -/
abbrev circleLift (f : ℝ → ℂ) : AddCircle (1 : ℝ) → ℂ := AddCircle.liftIco 1 0 f

theorem circleLift_coe {f : ℝ → ℂ} (hf : Function.Periodic f 1) (x : ℝ) :
    circleLift f (x : AddCircle (1 : ℝ)) = f x := by
  have hmem : Int.fract x ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    rw [zero_add]
    exact ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have hcoe : ((x : ℝ) : AddCircle (1 : ℝ)) = ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) := by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
    exact ⟨⌊x⌋, by rw [Int.self_sub_fract]; simp⟩
  rw [hcoe, circleLift, AddCircle.liftIco_coe_apply hmem]
  have := hf.sub_int_mul_eq (x := x) ⌊x⌋
  rw [mul_one] at this
  rw [Int.fract, this]

theorem continuous_circleLift {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hc : Continuous f) :
    Continuous (circleLift f) :=
  AddCircle.liftIco_continuous (by simpa using (hf 0).symm) hc.continuousOn

theorem fourierCoeff_circleLift (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (circleLift f) n =
      ∫ x in (0 : ℝ)..1, fourier (-n) (x : AddCircle (1 : ℝ)) * f x := by
  rw [circleLift, fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
  simp

/-- **Fourier coefficients of a derivative.**  For a `1`-periodic `f` with continuous derivative
`f'`, `\hat{f'}(n) = 2πi n \hat f(n)`. -/
theorem fourierCoeff_circleLift_deriv {f f' : ℝ → ℂ} (hf : Function.Periodic f 1)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f') (n : ℤ) :
    fourierCoeff (circleLift f') n = 2 * π * I * n * fourierCoeff (circleLift f) n := by
  have hf01 : f 1 = f 0 := by simpa using hf 0
  by_cases hn : n = 0
  · subst hn
    rw [fourierCoeff_circleLift]
    simp only [neg_zero, fourier_zero, one_mul, Int.cast_zero, mul_zero, zero_mul]
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable 0 1), hf01,
      sub_self]
  · have hab : (0 : ℝ) < 1 := one_pos
    have h := fourierCoeffOn_of_hasDerivAt hab hn (fun x _ => hd x) (hc.intervalIntegrable 0 1)
    rw [circleLift, circleLift, fourierCoeff_liftIco_eq, fourierCoeff_liftIco_eq]
    have hfc : fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) (zero_lt_one' ℝ)) f n =
        fourierCoeffOn hab f n := by
      simp only [fourierCoeffOn_eq_integral]; norm_num
    have hfc' : fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) (zero_lt_one' ℝ)) f' n =
        fourierCoeffOn hab f' n := by
      simp only [fourierCoeffOn_eq_integral]; norm_num
    rw [hfc, hfc', h, hf01, sub_self, mul_zero, zero_sub]
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    push_cast
    ring

/-- The `L²` class of a continuous periodic function. -/
def circleLiftLp {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hc : Continuous f) : CCMCircleL2 :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ ⟨circleLift f, continuous_circleLift hf hc⟩

theorem circleLiftLp_coeFn {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hc : Continuous f) :
    ((circleLiftLp hf hc : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      circleLift f :=
  ContinuousMap.coeFn_toLp _ _

theorem fourierCoeff_circleLiftLp {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hc : Continuous f) :
    fourierCoeff ((circleLiftLp hf hc : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =
      fourierCoeff (circleLift f) :=
  fourierCoeff_congr_ae (circleLiftLp_coeFn hf hc)

private theorem haarAddCircle_one_eq_volume :
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- **Parseval.**  For continuous `1`-periodic `f, g`,
`∫₀¹ \bar f g = ∑_n \overline{\hat f(n)} \hat g(n)`. -/
theorem tsum_conj_fourierCoeff_mul_fourierCoeff {f g : ℝ → ℂ}
    (hf : Function.Periodic f 1) (hfc : Continuous f)
    (hg : Function.Periodic g 1) (hgc : Continuous g) :
    ∑' n : ℤ, starRingEnd ℂ (fourierCoeff (circleLift f) n) * fourierCoeff (circleLift g) n =
      ∫ x in (0 : ℝ)..1, starRingEnd ℂ (f x) * g x := by
  have hP := (fourierBasis (T := (1 : ℝ))).tsum_inner_mul_inner
    (circleLiftLp hf hfc) (circleLiftLp hg hgc)
  have hrepr : ∀ (v : CCMCircleL2) (n : ℤ),
      inner ℂ ((fourierBasis (T := (1 : ℝ))) n) v =
        fourierCoeff ((v : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n := by
    intro v n
    rw [← (fourierBasis (T := (1 : ℝ))).repr_apply_apply, fourierBasis_repr]
  have hterm : ∀ n : ℤ,
      inner ℂ (circleLiftLp hf hfc) ((fourierBasis (T := (1 : ℝ))) n) *
          inner ℂ ((fourierBasis (T := (1 : ℝ))) n) (circleLiftLp hg hgc) =
        starRingEnd ℂ (fourierCoeff (circleLift f) n) * fourierCoeff (circleLift g) n := by
    intro n
    rw [← inner_conj_symm, hrepr, hrepr, fourierCoeff_circleLiftLp,
      fourierCoeff_circleLiftLp]
  simp_rw [hterm] at hP
  rw [hP, MeasureTheory.L2.inner_def]
  have hae : (fun z => inner ℂ (((circleLiftLp hf hfc : CCMCircleL2) :
        AddCircle (1 : ℝ) → ℂ) z) (((circleLiftLp hg hgc : CCMCircleL2) :
        AddCircle (1 : ℝ) → ℂ) z)) =ᵐ[AddCircle.haarAddCircle]
      fun z => starRingEnd ℂ (circleLift f z) * circleLift g z := by
    filter_upwards [circleLiftLp_coeFn hf hfc, circleLiftLp_coeFn hg hgc] with z h1 h2
    rw [h1, h2, RCLike.inner_apply', mul_comm]
  rw [integral_congr_ae hae, haarAddCircle_one_eq_volume]
  have hpre := AddCircle.intervalIntegral_preimage (1 : ℝ) 0
    (fun z => starRingEnd ℂ (circleLift f z) * circleLift g z)
  rw [zero_add] at hpre
  rw [← hpre]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [circleLift_coe hf, circleLift_coe hg]

/-- **Winding integral in Fourier form.**  For a `1`-periodic `f` with continuous derivative,
`∫₀¹ \bar f f' = 2πi ∑_n n |\hat f(n)|²`. -/
theorem integral_conj_mul_deriv_eq_tsum {f f' : ℝ → ℂ} (hf : Function.Periodic f 1)
    (hfc : Continuous f) (hd : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (hf' : Function.Periodic f' 1) :
    ∫ x in (0 : ℝ)..1, starRingEnd ℂ (f x) * f' x =
      2 * π * I * ((∑' n : ℤ, (n : ℝ) * ‖fourierCoeff (circleLift f) n‖ ^ 2 : ℝ) : ℂ) := by
  rw [← tsum_conj_fourierCoeff_mul_fourierCoeff hf hfc hf' hc, ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [fourierCoeff_circleLift_deriv hf hd hc n]
  have h : ((‖fourierCoeff (circleLift f) n‖ : ℂ)) ^ 2 =
      starRingEnd ℂ (fourierCoeff (circleLift f) n) * fourierCoeff (circleLift f) n := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  push_cast
  rw [h]
  ring

/-! ## `C²` phases -/

/-- The derivative of a periodic function is periodic. -/
theorem periodic_of_hasDerivAt {f f' : ℝ → ℂ} (hf : Function.Periodic f 1)
    (hd : ∀ x, HasDerivAt f (f' x) x) : Function.Periodic f' 1 := by
  intro x
  have h1 : HasDerivAt (fun y => f (y + 1)) (f' (x + 1)) x := by
    simpa using (hd (x + 1)).comp_add_const x 1
  have h2 : (fun y => f (y + 1)) = f := funext hf
  rw [h2] at h1
  exact h1.unique (hd x)

/-- A `C²` function lifted to the circle. -/
structure SmoothCircleFunction where
  f : ℝ → ℂ
  f' : ℝ → ℂ
  f'' : ℝ → ℂ
  periodic : Function.Periodic f 1
  hasDerivAt : ∀ x, HasDerivAt f (f' x) x
  hasDerivAt' : ∀ x, HasDerivAt f' (f'' x) x
  continuous'' : Continuous f''

namespace SmoothCircleFunction

variable (F : SmoothCircleFunction)

theorem continuous : Continuous F.f :=
  continuous_iff_continuousAt.mpr fun x => (F.hasDerivAt x).continuousAt

theorem continuous' : Continuous F.f' :=
  continuous_iff_continuousAt.mpr fun x => (F.hasDerivAt' x).continuousAt

theorem periodic' : Function.Periodic F.f' 1 := periodic_of_hasDerivAt F.periodic F.hasDerivAt

theorem periodic'' : Function.Periodic F.f'' 1 := periodic_of_hasDerivAt F.periodic' F.hasDerivAt'

theorem fourierCoeff_second (n : ℤ) :
    fourierCoeff (circleLift F.f'') n =
      (2 * π * I * n) ^ 2 * fourierCoeff (circleLift F.f) n := by
  rw [fourierCoeff_circleLift_deriv F.periodic' F.hasDerivAt' F.continuous'' n,
    fourierCoeff_circleLift_deriv F.periodic F.hasDerivAt F.continuous' n]
  ring

theorem norm_fourierCoeff_second (n : ℤ) :
    ‖fourierCoeff (circleLift F.f'') n‖ =
      4 * π ^ 2 * ((n : ℝ) ^ 2 * ‖fourierCoeff (circleLift F.f) n‖) := by
  rw [fourierCoeff_second, norm_mul, norm_pow]
  have : ‖(2 * π * I * n : ℂ)‖ = 2 * π * |(n : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [this, mul_pow, mul_pow, sq_abs]
  ring

/-- `∑ (n² |\hat f(n)|)² < ∞`, by Parseval for `f''`. -/
theorem summable_sq_mul_norm_sq :
    Summable fun n : ℤ => ((n : ℝ) ^ 2 * ‖fourierCoeff (circleLift F.f) n‖) ^ 2 := by
  have hP := (hasSum_sq_fourierCoeff (circleLiftLp F.periodic'' F.continuous'')).summable
  rw [fourierCoeff_circleLiftLp] at hP
  have hpi : (0 : ℝ) < (4 * π ^ 2) ^ 2 := by positivity
  refine (hP.div_const ((4 * π ^ 2) ^ 2)).congr fun n => ?_
  rw [norm_fourierCoeff_second, mul_pow]
  field_simp

private theorem moment_le_sq (k : ℝ) (hk : 1 ≤ k) (c : ℝ) :
    k * c ≤ ((k ^ 2 * c) ^ 2 + 1 / k ^ 2) / 2 := by
  have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
  have h := two_mul_le_add_sq (k ^ 2 * c) (1 / k)
  have e : 2 * (k ^ 2 * c) * (1 / k) = 2 * (k * c) := by field_simp
  rw [e, div_pow, one_pow] at h
  linarith

private theorem summable_first_moment_along {g : ℕ → ℤ}
    (hg : Function.Injective g) (habs : ∀ n : ℕ, |((g n : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ)) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff (circleLift F.f) (g n)‖ := by
  have hsq := F.summable_sq_mul_norm_sq.comp_injective hg
  have hinv : Summable fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hsq.add hinv).div_const 2)
  have hk : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have h := moment_le_sq _ hk ‖fourierCoeff (circleLift F.f) (g n)‖
  have hsq' : ((g n : ℝ)) ^ 2 = ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← sq_abs, habs n]
  simp only [Function.comp_apply]
  rw [hsq']
  exact h

theorem positiveMoment :
    Summable fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff (circleLift F.f) ((n + 1 : ℕ) : ℤ)‖ :=
  F.summable_first_moment_along (g := fun n => ((n + 1 : ℕ) : ℤ))
    (fun a b h => by simpa using h)
    (fun n => by push_cast; exact abs_of_nonneg (by positivity))

theorem negativeMoment :
    Summable fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff (circleLift F.f) (-((n + 1 : ℕ) : ℤ))‖ :=
  F.summable_first_moment_along (g := fun n => -((n + 1 : ℕ) : ℤ))
    (fun a b h => by simpa using h)
    (fun n => by push_cast; rw [abs_neg]; exact abs_of_nonneg (by positivity))

theorem summable_moment :
    Summable fun n : ℤ => (n : ℝ) * ‖fourierCoeff (circleLift F.f) n‖ ^ 2 := by
  refine Summable.of_norm_bounded F.summable_sq_mul_norm_sq fun n => ?_
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sq_nonneg ‖fourierCoeff (circleLift F.f) n‖), mul_pow, ← pow_mul]
  by_cases hn : n = 0
  · subst hn; simp
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    have h4 : |(n : ℝ)| ≤ (n : ℝ) ^ (2 * 2) := by
      rw [show (n : ℝ) ^ (2 * 2) = |(n : ℝ)| ^ 4 by
        rw [show 2 * 2 = 4 by norm_num, ← abs_pow, abs_of_nonneg (by positivity)]]
      calc |(n : ℝ)| = |(n : ℝ)| ^ 1 := (pow_one _).symm
        _ ≤ |(n : ℝ)| ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
    exact mul_le_mul_of_nonneg_right h4 (sq_nonneg _)

end SmoothCircleFunction

/-- A `C²` periodic function of modulus one, as a circle phase. -/
def SmoothCircleFunction.toPhase (F : SmoothCircleFunction) (hnorm : ∀ x, ‖F.f x‖ = 1) :
    CCMCirclePhase where
  toFun := circleLift F.f
  measurable := (continuous_circleLift F.periodic F.continuous).measurable
  norm_eq_one z := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [circleLift_coe F.periodic, hnorm]
  positiveMoment := F.positiveMoment
  negativeMoment := F.negativeMoment

theorem SmoothCircleFunction.toPhase_toFun (F : SmoothCircleFunction)
    (hnorm : ∀ x, ‖F.f x‖ = 1) : (F.toPhase hnorm).toFun = circleLift F.f := rfl

/-- The signed first moment is the full `ℤ`-indexed moment. -/
theorem SmoothCircleFunction.windingMoment_toPhase (F : SmoothCircleFunction)
    (hnorm : ∀ x, ‖F.f x‖ = 1) :
    (F.toPhase hnorm).windingMoment =
      ∑' n : ℤ, (n : ℝ) * ‖fourierCoeff (circleLift F.f) n‖ ^ 2 := by
  have hs := F.summable_moment
  set g : ℤ → ℝ := fun n => (n : ℝ) * ‖fourierCoeff (circleLift F.f) n‖ ^ 2 with hg
  have hnat : Summable fun n : ℕ => g n := hs.comp_injective Nat.cast_injective
  have hneg : Summable fun n : ℕ => g (-((n : ℤ) + 1)) :=
    hs.comp_injective (fun a b h => by simpa using h)
  rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add]
  have hpos : ∀ n : ℕ, g ((n + 1 : ℕ) : ℤ) =
      ((n + 1 : ℕ) : ℝ) * ‖fourierCoeff (circleLift F.f) ((n + 1 : ℕ) : ℤ)‖ ^ 2 := by
    intro n
    simp only [hg, Int.cast_natCast]
  have hneg' : ∀ n : ℕ, g (-((n : ℤ) + 1)) =
      -(((n + 1 : ℕ) : ℝ) * ‖fourierCoeff (circleLift F.f) (-((n + 1 : ℕ) : ℤ))‖ ^ 2) := by
    intro n
    have e : (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    simp only [hg]
    rw [e]
    push_cast
    ring
  have h0 : g ((0 : ℕ) : ℤ) = 0 := by simp [hg]
  simp only [hpos, hneg', h0, tsum_neg, zero_add]
  rw [CCMCirclePhase.windingMoment, F.toPhase_toFun hnorm]
  ring

/-- **Relative index of a smooth phase = its winding integral.**
`ind(M_f† P M_f, P) = (2πi)⁻¹ ∫₀¹ ar f f'`. -/
theorem SmoothCircleFunction.relativeIndex_toPhase_eq_integral (F : SmoothCircleFunction)
    (hnorm : ∀ x, ‖F.f x‖ = 1) :
    ((restrictedProjectionRelativeIndex (F.toPhase hnorm).datum.conjugateProjection
        (F.toPhase hnorm).datum.projection : ℤ) : ℂ) =
      (2 * π * I)⁻¹ * ∫ x in (0 : ℝ)..1, starRingEnd ℂ (F.f x) * F.f' x := by
  rw [integral_conj_mul_deriv_eq_tsum F.periodic F.continuous F.hasDerivAt F.continuous'
    F.periodic', ← F.windingMoment_toPhase hnorm,
    ← (F.toPhase hnorm).relativeIndex_eq_windingMoment]
  have hpi : (2 * π * I : ℂ) ≠ 0 := by
    have := Real.pi_ne_zero
    simp [this, I_ne_zero]
  field_simp
  push_cast
  ring

end RHTower
