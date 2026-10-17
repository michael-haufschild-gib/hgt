import GaloisForLFunctions.RHTower.CosDilationDivisorMomentPeriodizationRigidity
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.RHTower.EulerMaclaurinSawtooth
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# Blind cores are Nyman–Beurling wandering vectors

Let `f` be smooth and supported in `[α, β]` with `0 < α ≤ β` and `𝓜f(1) = ∫_0^∞ f = 0`, and let
`Ψ_f = cosDilationKernel f`.  The Nyman–Beurling sum of `f` is `F(x) = Σ_{k≥1} f(kx)` (`nbSum`).

* `abs_nbSum_le`: `|F| ≤ ½ ∫ |f'|` (first-order Euler–Maclaurin, using `∫ f = 0`), and `F` vanishes
  off `(0, β]`.
* `mellin_nbSum_of_one_lt`, `mellin_nbSum_eq`: `𝓜F(s) = ζ(s) 𝓜f(s)` for `Re s > 1`, and for
  `Re s > 0`, `Im s ≠ 0` by the identity theorem.
* `integral_norm_mellin_half_sq`: Mellin–Plancherel on the critical line,
  `∫ |𝓜G(½ + it)|² dt = 2π ∫_0^∞ |G|²`, for `G` continuous on `(0, ∞)`, bounded, and vanishing
  beyond some `β`.
* `integral_nbSum_mul_nbSum_dilate`: the Gram identity
  `∫_0^∞ F(x) F(nx) dx = Σ_{m≥1} d(m) Ψ_f(mn)` for `n ≥ 1`.
* `eq_zero_of_tsum_divisorCard_eq_zero`: the divisor transform `Ψ ↦ Σ_m d(m) Ψ(m·)` is injective on
  the integers `≥ 2` for kernels with `|Ψ(j)| ≤ C j⁻³`, because `Σ_{m≥2} m⁻² = π²/6 − 1 < 1`.
* `blind_iff_wandering`: `f` is blind (`Ψ_f(n) = 0` for all `n ≥ 2`) iff its Nyman–Beurling sum is
  orthogonal to all its integer dilates, `∫_0^∞ F(x) F(nx) dx = 0` for all `n ≥ 2`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real ContDiff FourierTransform

namespace RHTower.BlindCoreWandering

noncomputable section

variable {f : ℝ → ℝ} {α β : ℝ}

/-- The Nyman–Beurling sum `F(x) = Σ_{k≥1} f(kx)`. -/
def nbSum (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑' k : ℕ, f (((k : ℝ) + 1) * x)

theorem eq_zero_of_not_supp (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {y : ℝ}
    (hy : y < α ∨ β < y) : f y = 0 := by
  by_contra h
  have := hsupp y h
  rcases hy with hy | hy
  · linarith [this.1]
  · linarith [this.2]

theorem hasCompactSupport_of_supp (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun y hy => by
    rw [mem_Icc, not_and_or, not_le, not_le] at hy
    exact eq_zero_of_not_supp hsupp hy

theorem exists_nat_lt_mul {x : ℝ} (hx : 0 < x) (β : ℝ) : ∃ N : ℕ, β < N * x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (β / x)
  exact ⟨N, (div_lt_iff₀ hx).mp hN⟩

theorem nbSum_eq_sum (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {x : ℝ} (hx : 0 < x) {N : ℕ}
    (hN : β < N * x) : nbSum f x = ∑ k ∈ Finset.range N, f (((k : ℝ) + 1) * x) := by
  refine tsum_eq_sum fun k hk => eq_zero_of_not_supp hsupp (Or.inr ?_)
  have hk' : (N : ℝ) ≤ k := by exact_mod_cast not_lt.mp (Finset.mem_range.not.mp hk)
  nlinarith [mul_le_mul_of_nonneg_right hk' hx.le]

theorem nbSum_of_nonpos (hα : 0 < α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {x : ℝ}
    (hx : x ≤ 0) : nbSum f x = 0 := by
  have h : ∀ k : ℕ, f (((k : ℝ) + 1) * x) = 0 := fun k =>
    eq_zero_of_not_supp hsupp (Or.inl (by nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]))
  simp [nbSum, h]

theorem nbSum_of_lt (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {x : ℝ}
    (hx : β < x) : nbSum f x = 0 := by
  have hx0 : 0 < x := by linarith
  have h : ∀ k : ℕ, f (((k : ℝ) + 1) * x) = 0 := fun k =>
    eq_zero_of_not_supp hsupp (Or.inr (by nlinarith [mul_nonneg (k.cast_nonneg : (0 : ℝ) ≤ k) hx0.le]))
  simp [nbSum, h]

theorem continuousOn_nbSum (hf : Continuous f) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    ContinuousOn (nbSum f) (Ioi 0) := by
  intro x₀ hx₀
  have hx₀' : (0 : ℝ) < x₀ := hx₀
  obtain ⟨N, hN⟩ := exists_nat_lt_mul (half_pos hx₀') β
  have heq : (fun x => ∑ k ∈ Finset.range N, f (((k : ℝ) + 1) * x)) =ᶠ[𝓝 x₀] nbSum f := by
    filter_upwards [Ioi_mem_nhds (half_lt_self hx₀')] with x hx
    exact (nbSum_eq_sum hsupp ((half_pos hx₀').trans hx)
      (hN.trans_le (mul_le_mul_of_nonneg_left (le_of_lt hx) (Nat.cast_nonneg N)))).symm
  refine (ContinuousAt.congr ?_ heq).continuousWithinAt
  exact (continuous_finsetSum _ fun k _ => hf.comp (continuous_const.mul continuous_id)).continuousAt

/-- **First-order Euler–Maclaurin bound**: when `∫_0^∞ f = 0`, `|F(x)| ≤ ½ ∫ |f'|`. -/
theorem abs_nbSum_le (hf : ContDiff ℝ ∞ f) (hα : 0 < α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hint : ∫ y in Ioi (0 : ℝ), f y = 0) (x : ℝ) :
    |nbSum f x| ≤ (∫ y, |deriv f y|) / 2 := by
  have hV : 0 ≤ ∫ y, |deriv f y| := integral_nonneg fun _ => abs_nonneg _
  rcases le_or_gt x 0 with hx | hx
  · rw [nbSum_of_nonpos hα hsupp hx, abs_zero]; linarith
  obtain ⟨N, hN⟩ := exists_nat_lt_mul hx β
  have hcd : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hd : ∀ u, HasDerivAt (fun u => f (x * u)) (x * deriv f (x * u)) u := fun u => by
    have h := ((hf.differentiable (by simp)) (x * u)).hasDerivAt.comp u
      ((hasDerivAt_id u).const_mul x)
    simpa [Function.comp_def, mul_comm] using h
  have hEM := GaloisForLFunctions.RHTower.integral_fract_mul_deriv_eq
    (g := fun u => f (x * u)) (g' := fun u => x * deriv f (x * u)) N hd
    (continuous_const.mul (hcd.comp (continuous_const.mul continuous_id)))
  have hf0 : f 0 = 0 := eq_zero_of_not_supp hsupp (Or.inl hα)
  have hfN : f (x * N) = 0 := eq_zero_of_not_supp hsupp (Or.inr (by linarith [mul_comm x N]))
  have hsum : ∑ m ∈ Finset.range (N + 1), f (x * (m : ℝ)) = nbSum f x := by
    rw [Finset.sum_range_succ', nbSum_eq_sum hsupp hx hN]
    simp only [Nat.cast_zero, mul_zero, hf0, add_zero, Nat.cast_add, Nat.cast_one]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  have hzero : ∫ u in (0 : ℝ)..N, f (x * u) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (fun y => f y) hx.ne', mul_zero,
      intervalIntegral.integral_of_le (by positivity),
      ← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
        fun y hy => eq_zero_of_not_supp hsupp (Or.inr ?_), hint, smul_zero]
    have h1 : ¬ y ≤ x * N := fun h => hy.2 ⟨hy.1, h⟩
    linarith [mul_comm x N]
  simp only [hf0, mul_zero, hfN, hsum, hzero] at hEM
  have hEM' : nbSum f x = ∫ u in (0 : ℝ)..N, (Int.fract u - 1 / 2) * (x * deriv f (x * u)) := by
    rw [hEM]; ring
  rw [hEM']
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (Nat.cast_nonneg N)
    (g := fun u => 1 / 2 * (x * |deriv f (x * u)|))
    (f := fun u => (Int.fract u - 1 / 2) * (x * deriv f (x * u)))
    (Eventually.of_forall fun u _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx]
      have h1 : |Int.fract u - 1 / 2| ≤ 1 / 2 :=
        abs_le.mpr ⟨by linarith [Int.fract_nonneg u], by linarith [Int.fract_lt_one u]⟩
      exact mul_le_mul_of_nonneg_right h1 (by positivity))
    ((continuous_const.mul (continuous_const.mul
      ((hcd.comp (continuous_const.mul continuous_id)).abs))).intervalIntegrable (μ := volume) _ _)
  rw [Real.norm_eq_abs] at hbound
  refine hbound.trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun y => |deriv f y|) hx.ne', mul_zero, smul_eq_mul,
    ← mul_assoc x, mul_inv_cancel₀ hx.ne', one_mul, intervalIntegral.integral_of_le (by positivity)]
  have hi : Integrable fun y => |deriv f y| :=
    (hcd.integrable_of_hasCompactSupport (hasCompactSupport_of_supp hsupp).deriv).abs
  have := setIntegral_le_integral (μ := volume) (s := Ioc 0 (x * N)) hi
    (Eventually.of_forall fun y => abs_nonneg (deriv f y))
  linarith

/-! ### The Mellin transform of the Nyman–Beurling sum -/

theorem mellinConvergent_of_supp (hf : Continuous f) (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (s : ℂ) :
    MellinConvergent (fun t => (f t : ℂ)) s := by
  unfold MellinConvergent
  refine (ContinuousOn.integrableOn_compact (isCompact_Icc (a := α) (b := β))
    fun t ht => ?_).of_forall_sdiff_eq_zero measurableSet_Ioi fun t ht => ?_
  · have ht0 : t ≠ 0 := (lt_of_lt_of_le hα ht.1).ne'
    exact ((Complex.continuousAt_ofReal_cpow_const t _ (Or.inr ht0)).smul
      (Complex.continuous_ofReal.comp hf).continuousAt).continuousWithinAt
  · have h := ht.2
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    simp [eq_zero_of_not_supp hsupp h]

theorem integral_norm_mellin_term (s : ℂ) (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) • ((f (((k : ℝ) + 1) * x) : ℝ) : ℂ)‖ =
      (((k : ℝ) + 1) ^ s.re)⁻¹ * ∫ y in Ioi (0 : ℝ), y ^ (s.re - 1) * |f y| := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hc : ((k : ℝ) + 1) ^ (s.re - 1) ≠ 0 := by positivity
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) • ((f (((k : ℝ) + 1) * x) : ℝ) : ℂ)‖ =
      (((k : ℝ) + 1) ^ (s.re - 1))⁻¹ *
        ((((k : ℝ) + 1) * x) ^ (s.re - 1) * |f (((k : ℝ) + 1) * x)|) := by
    intro x hx
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
      Real.mul_rpow hk.le (le_of_lt hx), Complex.sub_re, Complex.one_re]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_comp_mul_left_Ioi (fun y => y ^ (s.re - 1) * |f y|) 0 hk, mul_zero, smul_eq_mul,
    ← mul_assoc]
  congr 1
  rw [Real.rpow_sub_one hk.ne']
  field_simp

/-- **`𝓜F = ζ · 𝓜f` on `Re s > 1`.** -/
theorem mellin_nbSum_of_one_lt (hf : Continuous f) (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) {s : ℂ} (hs : 1 < s.re) :
    mellin (fun x => (nbSum f x : ℂ)) s = riemannZeta s * mellin (fun y => (f y : ℂ)) s := by
  have hk : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hterm : ∀ k : ℕ, ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) • ((f (((k : ℝ) + 1) * x) : ℝ) : ℂ) =
      ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) * mellin (fun y => (f y : ℂ)) s := fun k =>
    mellin_comp_mul_left (fun y => (f y : ℂ)) s (hk k)
  have hint : ∀ k : ℕ, Integrable
      (fun x : ℝ => (x : ℂ) ^ (s - 1) • ((f (((k : ℝ) + 1) * x) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := fun k =>
    (MellinConvergent.comp_mul_left (f := fun y => (f y : ℂ)) (hk k)).mpr
      (mellinConvergent_of_supp hf hα hsupp s)
  have hsum : Summable fun k : ℕ =>
      ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) • ((f (((k : ℝ) + 1) * x) : ℝ) : ℂ)‖ := by
    simp_rw [integral_norm_mellin_term (f := f) s]
    refine Summable.mul_right _ ?_
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hs)
    refine h.congr fun k => ?_
    push_cast
    rfl
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hpt : ∀ x : ℝ, (x : ℂ) ^ (s - 1) • ((nbSum f x : ℝ) : ℂ) =
      ∑' k : ℕ, (x : ℂ) ^ (s - 1) • ((f (((k : ℝ) + 1) * x) : ℝ) : ℂ) := fun x => by
    simp only [smul_eq_mul]
    rw [nbSum, Complex.ofReal_tsum, tsum_mul_left]
  rw [mellin]
  simp_rw [hpt]
  rw [← hswap]
  simp_rw [hterm]
  rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  congr 1
  refine tsum_congr fun k => ?_
  rw [Complex.cpow_neg, one_div]
  push_cast
  rfl

theorem differentiableAt_mellin_of_supp (hf : Continuous f) (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (s : ℂ) :
    DifferentiableAt ℂ (mellin fun y => (f y : ℂ)) s := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    ((Complex.continuous_ofReal.comp hf).continuousOn.locallyIntegrableOn measurableSet_Ioi) ?_
    (by linarith)
    ?_ (by linarith)
  · have h : (fun _ : ℝ => (0 : ℂ)) =ᶠ[atTop] fun y => (f y : ℂ) := by
      filter_upwards [eventually_gt_atTop β] with y hy
      simp [eq_zero_of_not_supp hsupp (Or.inr hy)]
    exact (isBigO_zero (E' := ℂ) _ _).congr' h EventuallyEq.rfl
  · have h : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] 0] fun y => (f y : ℂ) := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hα)] with y hy
      simp [eq_zero_of_not_supp hsupp (Or.inl hy)]
    exact (isBigO_zero (E' := ℂ) _ _).congr' h EventuallyEq.rfl

theorem isBigO_nbSum_atTop (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (a : ℝ) : (fun x => (nbSum f x : ℂ)) =O[atTop] fun x : ℝ => x ^ (-a) := by
  have h : (fun _ : ℝ => (0 : ℂ)) =ᶠ[atTop] fun x => (nbSum f x : ℂ) := by
    filter_upwards [eventually_gt_atTop β] with x hx
    simp [nbSum_of_lt hα hαβ hsupp hx]
  exact (isBigO_zero (E' := ℂ) _ _).congr' h EventuallyEq.rfl

theorem isBigO_nbSum_zero (hf : ContDiff ℝ ∞ f) (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hint : ∫ y in Ioi (0 : ℝ), f y = 0) :
    (fun x => (nbSum f x : ℂ)) =O[𝓝[>] 0] fun x : ℝ => x ^ (-(0 : ℝ)) :=
  IsBigO.of_bound ((∫ y, |deriv f y|) / 2) (Eventually.of_forall fun x => by
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_nbSum_le hf hα hsupp hint x)

theorem differentiableAt_mellin_nbSum (hf : ContDiff ℝ ∞ f) (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hint : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (mellin fun x => (nbSum f x : ℂ)) s :=
  mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    ((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_nbSum hf.continuous hsupp)).locallyIntegrableOn measurableSet_Ioi)
    (isBigO_nbSum_atTop hα hαβ hsupp _) (by linarith) (isBigO_nbSum_zero hf hα hsupp hint) hs

theorem mellinConvergent_nbSum (hf : ContDiff ℝ ∞ f) (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hint : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent (fun x => (nbSum f x : ℂ)) s :=
  mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0)
    ((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_nbSum hf.continuous hsupp)).locallyIntegrableOn measurableSet_Ioi)
    (isBigO_nbSum_atTop hα hαβ hsupp _) (by linarith) (isBigO_nbSum_zero hf hα hsupp hint) hs

/-- **`𝓜F = ζ · 𝓜f` on `Re s > 0`, `Im s ≠ 0`** (identity theorem on the two quarter-planes). -/
theorem mellin_nbSum_eq (hf : ContDiff ℝ ∞ f) (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hint : ∫ y in Ioi (0 : ℝ), f y = 0) {s : ℂ}
    (hs : 0 < s.re) (him : s.im ≠ 0) :
    mellin (fun x => (nbSum f x : ℂ)) s = riemannZeta s * mellin (fun y => (f y : ℂ)) s := by
  have key : ∀ U : Set ℂ, IsOpen U → Convex ℝ U → (∀ z ∈ U, 0 < z.re ∧ z ≠ 1) →
      ∀ z₀ ∈ U, 1 < z₀.re →
        EqOn (mellin fun x => (nbSum f x : ℂ))
          (fun z => riemannZeta z * mellin (fun y => (f y : ℂ)) z) U := by
    intro U hUo hUc hU z₀ hz₀ hz₀re
    have hd1 : DifferentiableOn ℂ (mellin fun x => (nbSum f x : ℂ)) U := fun z hz =>
      (differentiableAt_mellin_nbSum hf hα hαβ hsupp hint (hU z hz).1).differentiableWithinAt
    have hd2 : DifferentiableOn ℂ (fun z => riemannZeta z * mellin (fun y => (f y : ℂ)) z) U :=
      fun z hz => ((differentiableAt_riemannZeta (hU z hz).2).mul
        (differentiableAt_mellin_of_supp hf.continuous hα hsupp z)).differentiableWithinAt
    refine (hd1.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hd2.analyticOnNhd hUo)
      hUc.isPreconnected hz₀ ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀re] with z hz
    exact mellin_nbSum_of_one_lt hf.continuous hα hsupp hz
  have hne : ∀ z : ℂ, z.im ≠ 0 → z ≠ 1 := fun z hz h => hz (by rw [h, Complex.one_im])
  rcases lt_or_gt_of_ne him with him | him
  · refine key {z | 0 < z.re ∧ z.im < 0}
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_im continuous_const))
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0))
      (fun z hz => ⟨hz.1, hne z hz.2.ne⟩) (2 - I) ⟨by simp, by simp⟩ (by simp)
      ⟨hs, him⟩
  · refine key {z | 0 < z.re ∧ 0 < z.im}
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im))
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0))
      (fun z hz => ⟨hz.1, hne z hz.2.ne'⟩) (2 + I) ⟨by simp, by simp⟩ (by simp)
      ⟨hs, him⟩

/-! ### Mellin–Plancherel on the critical line -/

/-- **Mellin–Plancherel on the critical line** for `G` continuous on `(0, ∞)`, bounded, and
vanishing beyond `β > 0`. -/
theorem integral_norm_mellin_half_sq {G : ℝ → ℂ} (hG : ContinuousOn G (Ioi 0)) {B β : ℝ}
    (hβ : 0 < β) (hB : ∀ x, ‖G x‖ ≤ B) (hsupp : ∀ x, β < x → G x = 0) :
    Integrable (fun t : ℝ => ‖mellin G (1 / 2 + t * I)‖ ^ 2) ∧
      ∫ t : ℝ, ‖mellin G (1 / 2 + t * I)‖ ^ 2 = 2 * π * ∫ x in Ioi (0 : ℝ), ‖G x‖ ^ 2 := by
  set h : ℝ → ℂ := fun u => Real.exp (-(1 / 2) * u) • G (Real.exp (-u)) with hh
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hmel : ∀ t : ℝ, mellin G (1 / 2 + t * I) = 𝓕 h (t / (2 * π)) := fun t => by
    rw [mellin_eq_fourier]
    have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
    have him : (1 / 2 + (t : ℂ) * I).im = t := by simp
    rw [hre, him]
  have hc : Continuous h :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (hG.comp_continuous (Real.continuous_exp.comp continuous_neg) fun u => Real.exp_pos _)
  have hzero : ∀ u, u < -Real.log β → h u = 0 := fun u hu => by
    have : β < Real.exp (-u) := (Real.log_lt_iff_lt_exp hβ).mp (by linarith)
    simp [hh, hsupp _ this]
  have hnorm : ∀ u, ‖h u‖ = Real.exp (-(1 / 2) * u) * ‖G (Real.exp (-u))‖ := fun u => by
    rw [hh, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : Integrable h := by
    have hdom : Integrable ((Ici (-Real.log β)).indicator
        fun u => B * Real.exp (-(1 / 2) * u)) :=
      (IntegrableOn.mono_set ((exp_neg_integrableOn_Ioi (-Real.log β - 1)
        (by norm_num : (0 : ℝ) < 1 / 2)).const_mul B) (Ici_subset_Ioi.mpr (by linarith))).integrable_indicator
        measurableSet_Ici
    refine hdom.mono' hc.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ Ici (-Real.log β)
    · rw [indicator_of_mem hu, hnorm, mul_comm]
      exact mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le
    · rw [indicator_of_notMem hu, hzero u (not_le.mp hu), norm_zero]
  have hsq : ∀ u, ‖h u‖ ^ 2 = Real.exp (-u) * ‖G (Real.exp (-u))‖ ^ 2 := fun u => by
    rw [hnorm, mul_pow, sq (Real.exp _), ← Real.exp_add]
    ring_nf
  have h2 : MemLp h 2 := by
    refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr ?_
    have hdom : Integrable ((Ici (-Real.log β)).indicator fun u => B ^ 2 * Real.exp (-1 * u)) :=
      (IntegrableOn.mono_set ((exp_neg_integrableOn_Ioi (-Real.log β - 1) one_pos).const_mul (B ^ 2))
        (Ici_subset_Ioi.mpr (by linarith))).integrable_indicator measurableSet_Ici
    refine hdom.mono' (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hu : u ∈ Ici (-Real.log β)
    · rw [indicator_of_mem hu, hsq, neg_one_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB _) 2)
        (Real.exp_pos _).le
    · rw [indicator_of_notMem hu, hzero u (not_le.mp hu), norm_zero]
      norm_num
  have hFT : MemLp (𝓕 h) 2 :=
    MemLp.ae_eq (GaloisForLFunctions.RHTower.coeFn_fourier_toLp h1 h2) (Lp.memLp _)
  have hFTi : Integrable fun ξ => ‖𝓕 h ξ‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hFT.1).mp hFT
  have hPl := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq h1 h2
  simp_rw [hmel]
  refine ⟨hFTi.comp_div (by positivity), ?_⟩
  rw [Measure.integral_comp_div (fun ξ => ‖𝓕 h ξ‖ ^ 2) (2 * π), abs_of_pos (by positivity),
    smul_eq_mul, hPl]
  simp_rw [hsq]
  congr 1
  have hneg := integral_neg_eq_self (fun v => Real.exp v * ‖G (Real.exp v)‖ ^ 2) volume
  rw [hneg, GaloisForLFunctions.HTGeometry.integral_Ioi_comp_exp fun z => ‖G z‖ ^ 2]

/-! ### Polarization: the Gram identity -/

theorem integrableOn_Ioi_of_bound {G : ℝ → ℝ} (hG : ContinuousOn G (Ioi 0)) {C β : ℝ}
    (hC : ∀ x, |G x| ≤ C) (hsupp : ∀ x, β < x → G x = 0) : IntegrableOn G (Ioi 0) := by
  have hc : IntegrableOn (fun _ : ℝ => C) (Ioc 0 β) := integrableOn_const measure_Ioc_lt_top.ne
  refine IntegrableOn.of_forall_sdiff_eq_zero (Integrable.mono' hc
    ((hG.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x))
    measurableSet_Ioi fun x hx => hsupp x ?_
  have h1 : ¬ x ≤ β := fun h => hx.2 ⟨hx.1, h⟩
  exact not_le.mp h1

/-- **Polarized Mellin–Plancherel**: for a real `F` continuous on `(0, ∞)`, bounded, vanishing
beyond `β`, and `n ≥ 1`,
`∫_0^∞ F(x) F(nx) dx = (1/2π) ∫ |𝓜F(½+it)|² Re n^{−(½+it)} dt`. -/
theorem integral_mul_dilate_eq {F : ℝ → ℝ} (hF : ContinuousOn F (Ioi 0)) {B β : ℝ} (hβ : 0 < β)
    (hB : ∀ x, |F x| ≤ B) (hsupp : ∀ x, β < x → F x = 0)
    (hconv : ∀ s : ℂ, 0 < s.re → MellinConvergent (fun x => (F x : ℂ)) s) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in Ioi (0 : ℝ), F x * F (n * x) =
      1 / (2 * π) * ∫ t : ℝ, ‖mellin (fun x => (F x : ℂ)) (1 / 2 + t * I)‖ ^ 2 *
        ((n : ℂ) ^ (-(1 / 2 + t * I))).re := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hFn : ContinuousOn (fun x => F (n * x)) (Ioi 0) :=
    hF.comp (continuous_const.mul continuous_id).continuousOn fun x hx =>
      mul_pos hn0 (show (0 : ℝ) < x from hx)
  have hsuppn : ∀ x, β < x → F (n * x) = 0 := fun x hx =>
    hsupp _ (by nlinarith [mul_le_mul_of_nonneg_right hn1 (hβ.le.trans hx.le)])
  -- the two polarization functions
  set Gp : ℝ → ℂ := fun x => ((F x + F (n * x) : ℝ) : ℂ) with hGp
  set Gm : ℝ → ℂ := fun x => ((F x - F (n * x) : ℝ) : ℂ) with hGm
  have hcp : ContinuousOn Gp (Ioi 0) := Complex.continuous_ofReal.comp_continuousOn (hF.add hFn)
  have hcm : ContinuousOn Gm (Ioi 0) := Complex.continuous_ofReal.comp_continuousOn (hF.sub hFn)
  have hbp : ∀ x, ‖Gp x‖ ≤ 2 * B := fun x => by
    rw [hGp, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_add_le (F x) (F (n * x)), hB x, hB (n * x)]
  have hbm : ∀ x, ‖Gm x‖ ≤ 2 * B := fun x => by
    rw [hGm, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_sub (F x) (F (n * x)), hB x, hB (n * x)]
  have hsp : ∀ x, β < x → Gp x = 0 := fun x hx => by simp [hGp, hsupp x hx, hsuppn x hx]
  have hsm : ∀ x, β < x → Gm x = 0 := fun x hx => by simp [hGm, hsupp x hx, hsuppn x hx]
  obtain ⟨hip, hPp⟩ := integral_norm_mellin_half_sq hcp hβ hbp hsp
  obtain ⟨him, hPm⟩ := integral_norm_mellin_half_sq hcm hβ hbm hsm
  -- the Mellin side
  have hmel : ∀ t : ℝ, ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      mellin (fun x => ((F x + ε * F (n * x) : ℝ) : ℂ)) (1 / 2 + t * I) =
        mellin (fun x => (F x : ℂ)) (1 / 2 + t * I) +
          (ε : ℂ) * ((n : ℂ) ^ (-(1 / 2 + t * I)) * mellin (fun x => (F x : ℂ)) (1 / 2 + t * I)) := by
    intro t ε _
    have hs : 0 < (1 / 2 + (t : ℂ) * I).re := by simp
    have h1 := hconv _ hs
    have h2 := (MellinConvergent.comp_mul_left (f := fun x => (F x : ℂ)) hn0).mpr h1
    have hdil := mellin_comp_mul_left (fun x => (F x : ℂ)) (1 / 2 + t * I) hn0
    rw [Complex.ofReal_natCast, smul_eq_mul] at hdil
    rw [← hdil]
    unfold mellin
    rw [← integral_const_mul, ← integral_add h1 (h2.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [smul_eq_mul]
    push_cast
    ring
  have hpt : ∀ t : ℝ, ‖mellin Gp (1 / 2 + t * I)‖ ^ 2 - ‖mellin Gm (1 / 2 + t * I)‖ ^ 2 =
      4 * (‖mellin (fun x => (F x : ℂ)) (1 / 2 + t * I)‖ ^ 2 *
        ((n : ℂ) ^ (-(1 / 2 + t * I))).re) := fun t => by
    have ep : Gp = fun x => ((F x + (1 : ℝ) * F (n * x) : ℝ) : ℂ) := by
      funext x; simp [hGp]
    have em : Gm = fun x => ((F x + (-1 : ℝ) * F (n * x) : ℝ) : ℂ) := by
      funext x; simp [hGm, sub_eq_add_neg]
    rw [ep, em, hmel t 1 (Or.inl rfl), hmel t (-1) (Or.inr rfl)]
    set M := mellin (fun x => (F x : ℂ)) (1 / 2 + t * I)
    set w := (n : ℂ) ^ (-(1 / 2 + t * I))
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- the real side
  have hreal : (∫ x in Ioi (0 : ℝ), ‖Gp x‖ ^ 2) - ∫ x in Ioi (0 : ℝ), ‖Gm x‖ ^ 2 =
      4 * ∫ x in Ioi (0 : ℝ), F x * F (n * x) := by
    have hsqp : ∀ x, ‖Gp x‖ ^ 2 = (F x + F (n * x)) ^ 2 := fun x => by
      rw [hGp, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hsqm : ∀ x, ‖Gm x‖ ^ 2 = (F x - F (n * x)) ^ 2 := fun x => by
      rw [hGm, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp_rw [hsqp, hsqm]
    have hip' : IntegrableOn (fun x => (F x + F (n * x)) ^ 2) (Ioi 0) :=
      integrableOn_Ioi_of_bound ((hF.add hFn).pow 2) (C := (2 * B) ^ 2) (β := β)
        (fun x => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (by linarith [abs_add_le (F x) (F (n * x)), hB x, hB (n * x)]) 2)
        fun x hx => by simp [hsupp x hx, hsuppn x hx]
    have him' : IntegrableOn (fun x => (F x - F (n * x)) ^ 2) (Ioi 0) :=
      integrableOn_Ioi_of_bound ((hF.sub hFn).pow 2) (C := (2 * B) ^ 2) (β := β)
        (fun x => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _)
            (by linarith [abs_sub (F x) (F (n * x)), hB x, hB (n * x)]) 2)
        fun x hx => by simp [hsupp x hx, hsuppn x hx]
    calc (∫ x in Ioi (0 : ℝ), (F x + F (n * x)) ^ 2) - ∫ x in Ioi (0 : ℝ), (F x - F (n * x)) ^ 2
        = ∫ x in Ioi (0 : ℝ), ((F x + F (n * x)) ^ 2 - (F x - F (n * x)) ^ 2) :=
          (integral_sub hip' him').symm
      _ = ∫ x in Ioi (0 : ℝ), 4 * (F x * F (n * x)) :=
          setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
      _ = 4 * ∫ x in Ioi (0 : ℝ), F x * F (n * x) := integral_const_mul _ _
  have hfin : ∫ t : ℝ, (‖mellin Gp (1 / 2 + t * I)‖ ^ 2 - ‖mellin Gm (1 / 2 + t * I)‖ ^ 2) =
      2 * π * (4 * ∫ x in Ioi (0 : ℝ), F x * F (n * x)) := by
    rw [show (∫ t : ℝ, (‖mellin Gp (1 / 2 + t * I)‖ ^ 2 - ‖mellin Gm (1 / 2 + t * I)‖ ^ 2)) =
        (∫ t : ℝ, ‖mellin Gp (1 / 2 + t * I)‖ ^ 2) - ∫ t : ℝ, ‖mellin Gm (1 / 2 + t * I)‖ ^ 2 from
          integral_sub hip him, hPp, hPm, ← mul_sub, hreal]
  have hI : ∫ t : ℝ, (‖mellin Gp (1 / 2 + t * I)‖ ^ 2 - ‖mellin Gm (1 / 2 + t * I)‖ ^ 2) =
      4 * ∫ t : ℝ, ‖mellin (fun x => (F x : ℂ)) (1 / 2 + t * I)‖ ^ 2 *
        ((n : ℂ) ^ (-(1 / 2 + t * I))).re := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have e := hfin.symm.trans hI
  rw [one_div, ← div_eq_inv_mul, eq_div_iff (by positivity)]
  linear_combination e / 4

/-- **Gram identity**: `∫_0^∞ F(x) F(nx) dx = Σ_m d(m) Ψ_f(mn)` for `n ≥ 1`. -/
theorem integral_nbSum_mul_nbSum_dilate (hf : ContDiff ℝ ∞ f) (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) {n : ℕ}
    (hn : 1 ≤ n) :
    ∫ x in Ioi (0 : ℝ), nbSum f x * nbSum f (n * x) =
      ∑' m : ℕ, (m.divisors.card : ℝ) * cosDilationKernel f ((m * n : ℕ) : ℝ) := by
  have hint := integral_Ioi_eq_zero_of_mellin_one_eq_zero h0
  have hβ : 0 < β := hα.trans_le hαβ
  have hn0 : 0 < n := by omega
  have hP := integral_mul_dilate_eq (F := nbSum f) (continuousOn_nbSum hf.continuous hsupp) hβ
    (abs_nbSum_le hf hα hsupp hint) (fun x hx => nbSum_of_lt hα hαβ hsupp hx)
    (fun s hs => mellinConvergent_nbSum hf hα hαβ hsupp hint hs) hn
  obtain ⟨hI, -⟩ := integral_norm_mellin_half_sq (G := fun x => (nbSum f x : ℂ))
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_nbSum hf.continuous hsupp)) hβ
    (B := (∫ y, |deriv f y|) / 2)
    (fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_nbSum_le hf hα hsupp hint x)
    (fun x hx => by simp [nbSum_of_lt hα hαβ hsupp hx])
  have hae : ∀ᵐ t : ℝ, mellin (fun x => (nbSum f x : ℂ)) (1 / 2 + t * I) =
      riemannZeta (1 / 2 + t * I) * mellin (fun y => (f y : ℂ)) (1 / 2 + t * I) := by
    have hne : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with t ht
    exact mellin_nbSum_eq hf hα hαβ hsupp hint (by simp) (by simpa using ht)
  have hD := integral_norm_zeta_mul_mellin_sq_mul_cpow_eq_tsum hf hα hαβ hsupp h0 hn
  set Z : ℝ → ℝ := fun t => ‖riemannZeta (1 / 2 + t * I) *
    mellin (fun y : ℝ => (f y : ℂ)) (1 / 2 + t * I)‖ ^ 2 with hZ
  have hZi : Integrable Z := hI.congr (hae.mono fun t ht => by simp only [hZ]; rw [ht])
  have hw : ∀ t : ℝ, ‖(n : ℂ) ^ (-(1 / 2 + t * I))‖ ≤ 1 := fun t => by
    rw [Complex.norm_natCast_cpow_of_pos hn0]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp)
  have hcw : Continuous fun t : ℝ => (n : ℂ) ^ (-(1 / 2 + t * I)) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).neg.const_cpow
      (Or.inl (by exact_mod_cast hn0.ne'))
  have hint2 : Integrable fun t : ℝ => ((Z t : ℝ) : ℂ) * (n : ℂ) ^ (-(1 / 2 + t * I)) := by
    refine hZi.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      hZi.aestronglyMeasurable).mul hcw.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (hw t)
  have h1 : ∫ t : ℝ, ‖mellin (fun x => (nbSum f x : ℂ)) (1 / 2 + t * I)‖ ^ 2 *
      ((n : ℂ) ^ (-(1 / 2 + t * I))).re =
        ∫ t : ℝ, (((Z t : ℝ) : ℂ) * (n : ℂ) ^ (-(1 / 2 + t * I))).re :=
    integral_congr_ae (hae.mono fun t ht => by dsimp only; rw [ht, Complex.re_ofReal_mul])
  have h2 := integral_re hint2
  simp only [RCLike.re_to_complex] at h2
  rw [hP, h1, h2, hD, Complex.ofReal_re]
  field_simp

/-- **Injectivity of the divisor transform on decaying kernels.**  If `|Ψ(j)| ≤ C j⁻³` and
`Σ_m d(m) Ψ(mn) = 0` for every `n ≥ 2`, then `Ψ(n) = 0` for every `n ≥ 2`: with
`M = sup_{j≥2} j³|Ψ(j)|`, the relation gives `n³|Ψ(n)| ≤ (π²/6 − 1) M` and `π²/6 − 1 < 1`. -/
theorem eq_zero_of_tsum_divisorCard_eq_zero {Ψ : ℕ → ℝ} {C : ℝ}
    (hΨ : ∀ j : ℕ, 1 ≤ j → |Ψ j| ≤ C / (j : ℝ) ^ 3)
    (hD : ∀ n : ℕ, 2 ≤ n → ∑' m : ℕ, (m.divisors.card : ℝ) * Ψ (m * n) = 0) :
    ∀ n : ℕ, 2 ≤ n → Ψ n = 0 := by
  set g : {j : ℕ // 2 ≤ j} → ℝ := fun j => (j.1 : ℝ) ^ 3 * |Ψ j.1| with hg
  have hgC : ∀ j, g j ≤ C := fun j => by
    have hj : (0 : ℝ) < (j.1 : ℝ) := by exact_mod_cast (by omega : 0 < j.1)
    have h := hΨ j.1 (by omega)
    rw [le_div_iff₀ (by positivity)] at h
    simp only [hg]
    linarith
  have hbdd : BddAbove (range g) := ⟨C, by rintro _ ⟨j, rfl⟩; exact hgC j⟩
  haveI : Nonempty {j : ℕ // 2 ≤ j} := ⟨⟨2, le_rfl⟩⟩
  set M := ⨆ j, g j with hM
  have hle : ∀ j : ℕ, 2 ≤ j → (j : ℝ) ^ 3 * |Ψ j| ≤ M := fun j hj => le_ciSup hbdd ⟨j, hj⟩
  have hM0 : 0 ≤ M := (by positivity : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ 3 * |Ψ 2|).trans (hle 2 le_rfl)
  have hz2 : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 2) ^ 2) (π ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one] at h
    norm_num at h
    simpa [Nat.cast_add] using h
  have hkey : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ^ 3 * |Ψ n| ≤ (π ^ 2 / 6 - 1) * M := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hterm : ∀ m : ℕ, ‖((m + 2 : ℕ).divisors.card : ℝ) * Ψ ((m + 2) * n)‖ ≤
        M / (n : ℝ) ^ 3 * (1 / ((m : ℝ) + 2) ^ 2) := by
      intro m
      have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
      have hd : ((m + 2 : ℕ).divisors.card : ℝ) ≤ (m : ℝ) + 2 := by
        have := Nat.card_divisors_le_self (m + 2)
        exact_mod_cast this
      have hΨb : |Ψ ((m + 2) * n)| ≤ M / (((m : ℝ) + 2) * n) ^ 3 := by
        have h := hle ((m + 2) * n) (by nlinarith)
        rw [le_div_iff₀ (by positivity)]
        push_cast at h
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc ((m + 2 : ℕ).divisors.card : ℝ) * |Ψ ((m + 2) * n)|
          ≤ ((m : ℝ) + 2) * (M / (((m : ℝ) + 2) * n) ^ 3) :=
            mul_le_mul hd hΨb (abs_nonneg _) hm.le
        _ = M / (n : ℝ) ^ 3 * (1 / ((m : ℝ) + 2) ^ 2) := by field_simp
    have hsumT : Summable fun m : ℕ => ((m + 2 : ℕ).divisors.card : ℝ) * Ψ ((m + 2) * n) :=
      Summable.of_norm_bounded (hz2.summable.mul_left _) hterm
    have hsum : Summable fun m : ℕ => (m.divisors.card : ℝ) * Ψ (m * n) :=
      (summable_nat_add_iff 2).mp hsumT
    have hsplit := (hsum.sum_add_tsum_nat_add 2).symm
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.divisors_zero,
      Finset.card_empty, Nat.cast_zero, zero_mul, zero_add, Nat.divisors_one, Finset.card_singleton,
      Nat.cast_one, one_mul] at hsplit
    rw [hD n hn] at hsplit
    have hΨn : Ψ n = -∑' m : ℕ, ((m + 2 : ℕ).divisors.card : ℝ) * Ψ ((m + 2) * n) := by
      linarith
    have hT := tsum_of_norm_bounded (hz2.mul_left (M / (n : ℝ) ^ 3)) hterm
    rw [Real.norm_eq_abs] at hT
    rw [hΨn, abs_neg]
    calc (n : ℝ) ^ 3 * |∑' m : ℕ, ((m + 2 : ℕ).divisors.card : ℝ) * Ψ ((m + 2) * n)|
        ≤ (n : ℝ) ^ 3 * (M / (n : ℝ) ^ 3 * (π ^ 2 / 6 - 1)) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = (π ^ 2 / 6 - 1) * M := by field_simp
  have hc : π ^ 2 / 6 - 1 < 1 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hMle : M ≤ (π ^ 2 / 6 - 1) * M := ciSup_le fun j => hkey j.1 j.2
  have hM : M ≤ 0 := by nlinarith
  intro n hn
  have h := (hle n hn).trans hM
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have : |Ψ n| ≤ 0 := by nlinarith [abs_nonneg (Ψ n)]
  exact abs_nonpos_iff.mp this

/-- **Blind cores are Nyman–Beurling wandering vectors.**  A smooth core `f` (support in
`[α, β]`, `0 < α`, `𝓜f(1) = 0`) is blind, `Ψ_f(n) = 0` for every `n ≥ 2`, iff its Nyman–Beurling
sum `F(x) = Σ_{k≥1} f(kx)` (with `𝓜F = ζ 𝓜f`) is orthogonal to all of its integer dilates:
`∫_0^∞ F(x) F(nx) dx = 0` for every `n ≥ 2`. -/
theorem blind_iff_wandering (hf : ContDiff ℝ ∞ f) (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (h0 : mellin (fun y : ℝ => (f y : ℂ)) 1 = 0) :
    (∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) ↔
      ∀ n : ℕ, 2 ≤ n → ∫ x in Ioi (0 : ℝ), nbSum f x * nbSum f (n * x) = 0 := by
  constructor
  · intro hb n hn
    rw [integral_nbSum_mul_nbSum_dilate hf hα hαβ hsupp h0 (by omega : 1 ≤ n)]
    refine (tsum_congr fun m => ?_).trans tsum_zero
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [hb (m * n) (by nlinarith), mul_zero]
  · intro hw
    set K := (∫ t : ℝ, ‖ExactNullDivisorTransfer.archXi (3 + t * I) ^ 2 *
      cosDilationCertMultiplier f (3 + t * I)‖) / (2 * π)
    refine eq_zero_of_tsum_divisorCard_eq_zero (Ψ := fun j : ℕ => cosDilationKernel f j) (C := K)
      (fun j hj => ?_) fun n hn => ?_
    · have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      have hb := ExactNullDivisorTransfer.norm_certKernel_le (cosDilationCertMultiplier f) hj0
      rw [certKernel_cosDilationCertMultiplier hf hα hαβ hsupp h0 hj0, Complex.norm_real,
        Real.norm_eq_abs, Real.rpow_neg hj0.le] at hb
      have e : (j : ℝ) ^ (3 : ℝ) = (j : ℝ) ^ (3 : ℕ) := by norm_cast
      rw [e] at hb
      show |cosDilationKernel f j| ≤ K / (j : ℝ) ^ 3
      rw [div_eq_mul_inv]
      exact hb
    · have h := integral_nbSum_mul_nbSum_dilate hf hα hαβ hsupp h0 (n := n) (by omega)
      rw [hw n hn] at h
      exact h.symm

end

end RHTower.BlindCoreWandering
