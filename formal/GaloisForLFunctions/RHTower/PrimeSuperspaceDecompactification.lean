import GaloisForLFunctions.RHTower.PrimeSuperspaceWickAnisotropy
import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence
import GaloisForLFunctions.RHTower.PrimeZetaOneLineConvergence
import GaloisForLFunctions.RHTower.PrimeScreenAlmostPeriodicNoGo
import GaloisForLFunctions.RHTower.MertensSecondPrimeRecipSum
import GaloisForLFunctions.HTGeometry.PrimeBooleanMassHankelQuantumFusion

/-!
# Thermodynamic decompactification of the prime clock
-/

namespace RHTower

open Filter
open scoped Topology BigOperators

theorem sum_primesLE_eq_filter {F : ℕ → ℝ} (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, F p = ∑ n ∈ Finset.Icc 0 N with n.Prime, F n := by
  classical
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨Nat.zero_le _, h1⟩, h2⟩
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨h1, h2⟩

/-! ## Finite clock recurrence -/

theorem norm_sq_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ (2 : ℕ) = 2 * (1 - Real.cos θ) := by
  have hexp : Complex.exp ((θ : ℂ) * Complex.I)
      = ⟨Real.cos θ, Real.sin θ⟩ := by
    rw [Complex.exp_mul_I]
    apply Complex.ext <;>
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
        Complex.sin_ofReal_im]
  rw [hexp, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **Finite clock recurrence.**  For every finite prime cutoff the clock energy returns below any
threshold at arbitrarily late times:  the finite prime phase flow is uniformly recurrent. -/
theorem exists_large_small_primeClockVerticalEnergy (N : ℕ) {η : ℝ} (hη : 0 < η) {T : ℝ}
    (hT : 0 < T) :
    ∃ h : ℝ, T ≤ h ∧ primeClockVerticalEnergy N h < η := by
  classical
  set S : ℝ := ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ with hS
  have hS0 : 0 ≤ S := by
    refine Finset.sum_nonneg fun p hp => ?_
    positivity
  set ε : ℝ := Real.sqrt (η / (S + 1)) with hε
  have hεpos : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hεsq : ε ^ (2 : ℕ) = η / (S + 1) := Real.sq_sqrt (by positivity)
  obtain ⟨t, hT', hclose⟩ :=
    HTGeometry.primeBooleanFusion_exists_large_return
      ((Nat.primesLE N).subtype Nat.Prime) hεpos hT
  refine ⟨t, hT', ?_⟩
  have hterm : ∀ p ∈ Nat.primesLE N,
      2 * (1 - Real.cos (t * Real.log p)) / (p : ℝ) ≤ ε ^ (2 : ℕ) * (p : ℝ)⁻¹ := by
    intro p hp
    have hprime : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    have hmem : (⟨p, hprime⟩ : Nat.Primes) ∈ (Nat.primesLE N).subtype Nat.Prime := by
      simpa [Finset.mem_subtype] using hp
    have hbound := hclose ⟨⟨p, hprime⟩, hmem⟩
    have hflow : HTGeometry.ConstraintFrameRelativity.shellFlow
        (F := (Nat.primesLE N).subtype Nat.Prime) 1 t ⟨⟨p, hprime⟩, hmem⟩
        = Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) := by
      rw [HTGeometry.ConstraintFrameRelativity.shellFlow,
        HTGeometry.ConstraintFrameRelativity.shellGenerator,
        HTGeometry.ConstraintFrameRelativity.primeClockVec]
      norm_num
    rw [hflow] at hbound
    have hsq : ‖Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) - 1‖ ^ (2 : ℕ) < ε ^ (2 : ℕ) := by
      refine pow_lt_pow_left₀ hbound (norm_nonneg _) (by norm_num)
    rw [norm_sq_exp_mul_I_sub_one] at hsq
    have hcos : Real.cos (-(t * Real.log p)) = Real.cos (t * Real.log p) := Real.cos_neg _
    rw [hcos] at hsq
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hsq.le (by positivity)
  have hsum : primeClockVerticalEnergy N t ≤ ε ^ (2 : ℕ) * S := by
    rw [primeClockVerticalEnergy_eq_cos, hS, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  refine lt_of_le_of_lt hsum ?_
  rw [hεsq]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-! ## Radial coercivity -/

/-- The finite radial reflection energy `R_N(r) = 2 ∑_{p ≤ N} (cosh(r log p) - 1)/p`. -/
noncomputable def primeClockRadialEnergy (N : ℕ) (r : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, 2 * (Real.cosh (r * Real.log p) - 1) / p

theorem primeClockRadialEnergy_term_nonneg (r : ℝ) {p : ℕ} (hp : p ∈ Nat.primesLE N) :
    0 ≤ 2 * (Real.cosh (r * Real.log p) - 1) / p := by
  have hprime : Nat.Prime p := (Nat.mem_primesLE.mp hp).2
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hcosh : (1 : ℝ) ≤ Real.cosh (r * Real.log p) := Real.one_le_cosh _
  have hnum : (0 : ℝ) ≤ 2 * (Real.cosh (r * Real.log p) - 1) := by linarith
  positivity

/-- **Radial coercivity.**  For every cutoff past the first prime the radial energy is unbounded. -/
theorem tendsto_primeClockRadialEnergy_atTop {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun r : ℝ => primeClockRadialEnergy N r) atTop atTop := by
  classical
  have hmem : (2 : ℕ) ∈ Nat.primesLE N := Nat.mem_primesLE.mpr ⟨hN, Nat.prime_two⟩
  have hlow : ∀ r : ℝ, (Real.cosh (r * Real.log 2) - 1) ≤ primeClockRadialEnergy N r := by
    intro r
    have hsingle : 2 * (Real.cosh (r * Real.log (2 : ℕ)) - 1) / ((2 : ℕ) : ℝ)
        = Real.cosh (r * Real.log 2) - 1 := by
      norm_num
    rw [primeClockRadialEnergy, ← hsingle]
    refine Finset.single_le_sum (f := fun p : ℕ => 2 * (Real.cosh (r * Real.log p) - 1) / p)
      (fun p hp => primeClockRadialEnergy_term_nonneg (N := N) r hp) hmem
  refine tendsto_atTop_mono hlow ?_
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : Tendsto (fun r : ℝ => r * Real.log 2) atTop atTop :=
    Filter.tendsto_id.atTop_mul_const hlog2
  have hcoshTop : Tendsto Real.cosh atTop atTop := by
    have hexp : Tendsto (fun x : ℝ => Real.exp x / 2) atTop atTop :=
      Real.tendsto_exp_atTop.atTop_div_const (by norm_num)
    refine tendsto_atTop_mono (fun x => ?_) hexp
    rw [Real.cosh_eq]
    have hpos : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
    linarith
  have hcomp : Tendsto (fun r : ℝ => Real.cosh (r * Real.log 2)) atTop atTop :=
    hcoshTop.comp hmul
  have hshift := tendsto_atTop_add_const_right atTop (-1 : ℝ) hcomp
  exact hshift.congr fun r => by ring

/-! ## The thermodynamic sharp law -/

theorem re_logPhase (lam t : ℝ) : (logPhase lam t).re = Real.cos (lam * Real.log t) := by
  have hEq : logPhase lam t = Complex.exp (((-(lam * Real.log t) : ℝ) : ℂ) * Complex.I) := by
    rw [logPhase]
    congr 1
    push_cast
    ring
  rw [hEq, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem primeClockVerticalEnergy_eq_recipSum_sub (N : ℕ) (h : ℝ) :
    primeClockVerticalEnergy N h
      = 2 * primeRecipSum N - 2 * (primePhaseSum h (N : ℝ)).re := by
  classical
  have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
  have hphase : (primePhaseSum h (N : ℝ)).re
      = ∑ n ∈ Finset.Icc 0 N with n.Prime, Real.cos (h * Real.log n) / (n : ℝ) := by
    rw [primePhaseSum_eq_cpow_sum, hfloor, Complex.re_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hprime : n.Prime := (Finset.mem_filter.mp hn).2
    rw [natCast_cpow_neg_one_sub h hprime.pos]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, re_logPhase]
    have him : (logPhase h (n : ℝ)).im = -Real.sin (h * Real.log n) := by
      have hEq : logPhase h (n : ℝ)
          = Complex.exp (((-(h * Real.log n) : ℝ) : ℂ) * Complex.I) := by
        rw [logPhase]
        congr 1
        push_cast
        ring
      rw [hEq, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    rw [him]
    ring
  have hrecip : primeRecipSum N = ∑ n ∈ Finset.Icc 0 N with n.Prime, (1 : ℝ) / (n : ℝ) := by
    rw [primeRecipSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n.Prime
    · rw [if_pos hn, primeRecipWeight, if_pos hn, one_div]
    · rw [if_neg hn, primeRecipWeight, if_neg hn]
  rw [primeClockVerticalEnergy_eq_cos, sum_primesLE_eq_filter, hphase, hrecip,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hprime : n.Prime := (Finset.mem_filter.mp hn).2
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hprime.pos
  field_simp

/-- **The thermodynamic sharp law `(18)`.**  For every fixed nonzero height the finite clock
energy is `2 log log N + 2B_1 - 2 Re C(h) + o(1)`, where `C(h)` is the convergent boundary
prime sum. -/
theorem exists_tendsto_primeClockVerticalEnergy_sub_logLog {h : ℝ} (hh : h ≠ 0) :
    ∃ C : ℂ, Tendsto (fun N : ℕ => primeClockVerticalEnergy N h - 2 * Real.log (Real.log N))
      atTop (𝓝 (2 * mertensSecondConstant - 2 * C.re)) := by
  obtain ⟨C, hC⟩ := exists_tendsto_primePhaseSum hh
  refine ⟨C, ?_⟩
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hCN : Tendsto (fun N : ℕ => (primePhaseSum h (N : ℝ)).re) atTop (𝓝 C.re) :=
    (Complex.continuous_re.tendsto _).comp (hC.comp hnat)
  have hM := tendsto_primeRecipSum_sub_logLog
  have hsum := (hM.const_mul 2).sub (hCN.const_mul 2)
  refine hsum.congr fun N => ?_
  rw [primeClockVerticalEnergy_eq_recipSum_sub]
  ring

/-- **Decompactification `(20)`.**  Every fixed nonzero clock displacement has divergent energy in
the all-prime limit, while every finite cutoff is recurrent. -/
theorem tendsto_primeClockVerticalEnergy_atTop {h : ℝ} (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => primeClockVerticalEnergy N h) atTop atTop := by
  obtain ⟨C, hC⟩ := exists_tendsto_primeClockVerticalEnergy_sub_logLog hh
  have hlogTop : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hmul : Tendsto (fun N : ℕ => 2 * Real.log (Real.log (N : ℝ))) atTop atTop :=
    hlogTop.const_mul_atTop (by norm_num)
  have hadd := hC.add_atTop hmul
  exact hadd.congr fun N => by ring

/-- **The overlap law `(19)`.**  The normalized coherent overlap `exp(-V_N(h)/2)` decays at the
exact rate `1/log N`, with the boundary constant as prefactor. -/
theorem exists_tendsto_exp_neg_half_primeClockVerticalEnergy_mul_log {h : ℝ} (hh : h ≠ 0) :
    ∃ C : ℂ, Tendsto
      (fun N : ℕ => Real.exp (-(primeClockVerticalEnergy N h) / 2) * Real.log (N : ℝ))
      atTop (𝓝 (Real.exp (C.re - mertensSecondConstant))) := by
  obtain ⟨C, hC⟩ := exists_tendsto_primeClockVerticalEnergy_sub_logLog hh
  refine ⟨C, ?_⟩
  have hexp := (Real.continuous_exp.tendsto _).comp (hC.const_mul (-(1 : ℝ) / 2))
  have hval : -(1 : ℝ) / 2 * (2 * mertensSecondConstant - 2 * C.re)
      = C.re - mertensSecondConstant := by ring
  rw [Function.comp_def] at hexp
  rw [hval] at hexp
  refine hexp.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 1] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hkey : -(1 : ℝ) / 2 * (primeClockVerticalEnergy N h - 2 * Real.log (Real.log (N : ℝ)))
      = -(primeClockVerticalEnergy N h) / 2 + Real.log (Real.log (N : ℝ)) := by ring
  rw [hkey, Real.exp_add, Real.exp_log hlogpos]

/-! ## The limiting Wick profiles -/

/-- The radial profile test function `2(cosh(cu)-1)/u`, extended by zero at the origin. -/
noncomputable def radialProfileTest (c : ℝ) (u : ℝ) : ℝ :=
  if u = 0 then 0 else 2 * (Real.cosh (c * u) - 1) / u

/-- The vertical profile test function `2(1-cos(cu))/u`, extended by zero at the origin. -/
noncomputable def verticalProfileTest (c : ℝ) (u : ℝ) : ℝ :=
  if u = 0 then 0 else 2 * (1 - Real.cos (c * u)) / u

theorem tendsto_radialProfileTest_punctured (c : ℝ) :
    Tendsto (radialProfileTest c) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hinner : HasDerivAt (fun u : ℝ => c * u) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have hd : HasDerivAt (fun u : ℝ => Real.cosh (c * u)) (Real.sinh (c * 0) * c) 0 :=
    (Real.hasDerivAt_cosh (c * 0)).comp 0 hinner
  rw [mul_zero, Real.sinh_zero, zero_mul] at hd
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hmul := hslope.const_mul (2 : ℝ)
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := hu
  rw [radialProfileTest, if_neg hu0, slope_def_field, mul_zero, Real.cosh_zero, sub_zero]
  ring

theorem tendsto_verticalProfileTest_punctured (c : ℝ) :
    Tendsto (verticalProfileTest c) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hinner : HasDerivAt (fun u : ℝ => c * u) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have hd : HasDerivAt (fun u : ℝ => Real.cos (c * u)) (-Real.sin (c * 0) * c) 0 :=
    (Real.hasDerivAt_cos (c * 0)).comp 0 hinner
  rw [mul_zero, Real.sin_zero, neg_zero, zero_mul] at hd
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hmul := hslope.const_mul (-2 : ℝ)
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := hu
  rw [verticalProfileTest, if_neg hu0, slope_def_field, mul_zero, Real.cos_zero, sub_zero]
  ring

theorem continuousOn_radialProfileTest (c : ℝ) :
    ContinuousOn (radialProfileTest c) (Set.Icc 0 1) := by
  intro u _
  by_cases hu0 : u = 0
  · subst hu0
    refine ContinuousAt.continuousWithinAt ?_
    rw [← continuousWithinAt_compl_self]
    have hval : radialProfileTest c 0 = 0 := by simp [radialProfileTest]
    rw [ContinuousWithinAt, hval]
    exact tendsto_radialProfileTest_punctured c
  · refine ContinuousAt.continuousWithinAt ?_
    have heq : (fun v : ℝ => 2 * (Real.cosh (c * v) - 1) / v) =ᶠ[𝓝 u] radialProfileTest c := by
      filter_upwards [isOpen_ne.mem_nhds hu0] with v hv
      rw [radialProfileTest, if_neg hv]
    refine ContinuousAt.congr ?_ heq
    exact ((Real.continuous_cosh.continuousAt.comp
      (continuousAt_id.const_mul c)).sub continuousAt_const).const_mul 2
      |>.div continuousAt_id hu0

theorem continuousOn_verticalProfileTest (c : ℝ) :
    ContinuousOn (verticalProfileTest c) (Set.Icc 0 1) := by
  intro u _
  by_cases hu0 : u = 0
  · subst hu0
    refine ContinuousAt.continuousWithinAt ?_
    rw [← continuousWithinAt_compl_self]
    have hval : verticalProfileTest c 0 = 0 := by simp [verticalProfileTest]
    rw [ContinuousWithinAt, hval]
    exact tendsto_verticalProfileTest_punctured c
  · refine ContinuousAt.continuousWithinAt ?_
    have heq : (fun v : ℝ => 2 * (1 - Real.cos (c * v)) / v) =ᶠ[𝓝 u] verticalProfileTest c := by
      filter_upwards [isOpen_ne.mem_nhds hu0] with v hv
      rw [verticalProfileTest, if_neg hv]
    refine ContinuousAt.congr ?_ heq
    exact (continuousAt_const.sub (Real.continuous_cos.continuousAt.comp
      (continuousAt_id.const_mul c))).const_mul 2 |>.div continuousAt_id hu0

theorem primeClockRadialEnergy_scaled_eq (c : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    primeClockRadialEnergy N (c / Real.log N)
      = mertensPrimeWindow (radialProfileTest c) N / Real.log N := by
  classical
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  rw [primeClockRadialEnergy, sum_primesLE_eq_filter, mertensPrimeWindow, Finset.sum_div,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hu : Real.log (n : ℝ) / Real.log (N : ℝ) ≠ 0 := by positivity
    rw [if_pos hp, mertensPrimeWeight, if_pos hp, radialProfileTest, if_neg hu]
    have harg : c * (Real.log (n : ℝ) / Real.log (N : ℝ))
        = c / Real.log (N : ℝ) * Real.log (n : ℝ) := by ring
    rw [harg]
    field_simp
  · rw [if_neg hp, mertensPrimeWeight, if_neg hp, mul_zero, zero_div]

theorem primeClockVerticalEnergy_scaled_eq (c : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    primeClockVerticalEnergy N (c / Real.log N)
      = mertensPrimeWindow (verticalProfileTest c) N / Real.log N := by
  classical
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  rw [primeClockVerticalEnergy_eq_cos, sum_primesLE_eq_filter, mertensPrimeWindow, Finset.sum_div,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hu : Real.log (n : ℝ) / Real.log (N : ℝ) ≠ 0 := by positivity
    rw [if_pos hp, mertensPrimeWeight, if_pos hp, verticalProfileTest, if_neg hu]
    have harg : c * (Real.log (n : ℝ) / Real.log (N : ℝ))
        = c / Real.log (N : ℝ) * Real.log (n : ℝ) := by ring
    rw [harg]
    field_simp
  · rw [if_neg hp, mertensPrimeWeight, if_neg hp, mul_zero, zero_div]

/-- **The limiting radial profile `(9)`.** -/
theorem tendsto_primeClockRadialEnergy_scaled (c : ℝ) :
    Tendsto (fun N : ℕ => primeClockRadialEnergy N (c / Real.log (N : ℝ))) atTop
      (𝓝 (∫ u in (0 : ℝ)..1, radialProfileTest c u)) := by
  have h := tendsto_mertensPrimeWindow_div_log (continuousOn_radialProfileTest c)
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  exact (primeClockRadialEnergy_scaled_eq c hN).symm

/-- **The limiting vertical profile `(10)`.** -/
theorem tendsto_primeClockVerticalEnergy_scaled (c : ℝ) :
    Tendsto (fun N : ℕ => primeClockVerticalEnergy N (c / Real.log (N : ℝ))) atTop
      (𝓝 (∫ u in (0 : ℝ)..1, verticalProfileTest c u)) := by
  have h := tendsto_mertensPrimeWindow_div_log (continuousOn_verticalProfileTest c)
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  exact (primeClockVerticalEnergy_scaled_eq c hN).symm

/-! ## The exact Wick relation -/

/-- The complex Wick profile integrand. -/
noncomputable def wickProfileTest (z : ℂ) (u : ℝ) : ℂ :=
  if u = 0 then 0 else 2 * (Complex.cosh (z * (u : ℂ)) - 1) / (u : ℂ)

/-- The Wick profile germ `Φ(z) = 2 ∫_0^(1 : ℕ) (cosh(zu) - 1)/u du`. -/
noncomputable def wickProfile (z : ℂ) : ℂ := ∫ u in (0 : ℝ)..1, wickProfileTest z u

theorem wickProfile_ofReal (c : ℝ) :
    wickProfile ((c : ℝ) : ℂ) = ((∫ u in (0 : ℝ)..1, radialProfileTest c u : ℝ) : ℂ) := by
  rw [wickProfile, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun u _ => ?_
  by_cases hu : u = 0
  · simp [wickProfileTest, radialProfileTest, hu]
  · rw [wickProfileTest, if_neg hu, radialProfileTest, if_neg hu]
    push_cast [Complex.ofReal_cosh]
    ring

theorem wickProfile_mul_I (c : ℝ) :
    wickProfile (((c : ℝ) : ℂ) * Complex.I)
      = -((∫ u in (0 : ℝ)..1, verticalProfileTest c u : ℝ) : ℂ) := by
  rw [wickProfile, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun u _ => ?_
  by_cases hu : u = 0
  · simp [wickProfileTest, verticalProfileTest, hu]
  · rw [wickProfileTest, if_neg hu, verticalProfileTest, if_neg hu]
    have hcosh : Complex.cosh (((c : ℝ) : ℂ) * Complex.I * (u : ℂ))
        = ((Real.cos (c * u) : ℝ) : ℂ) := by
      have harg : ((c : ℝ) : ℂ) * Complex.I * (u : ℂ) = (((c * u : ℝ)) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.cosh_mul_I, ← Complex.ofReal_cos]
    rw [hcosh]
    push_cast
    ring

/-- The Wick profile power-series terms. -/
noncomputable def wickProfileSeries (z : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  2 * z ^ (2 * (n + 1)) * ((u : ℂ)) ^ (2 * n + 1) / (((2 * (n + 1)).factorial : ℕ) : ℂ)

theorem hasSum_wickProfileSeries {z : ℂ} {u : ℝ} (hu : u ≠ 0) :
    HasSum (fun n : ℕ => wickProfileSeries z n u) (wickProfileTest z u) := by
  have huC : ((u : ℝ) : ℂ) ≠ 0 := by simpa using hu
  have hcosh := Complex.hasSum_cosh (z * (u : ℂ))
  have h : HasSum (fun n : ℕ =>
      (z * (u : ℂ)) ^ (2 * (n + 1)) / (((2 * (n + 1)).factorial : ℕ) : ℂ))
      (Complex.cosh (z * (u : ℂ)) - 1) := by
    refine (hasSum_nat_add_iff
      (f := fun n : ℕ => (z * (u : ℂ)) ^ (2 * n) / (((2 * n).factorial : ℕ) : ℂ)) 1).mpr ?_
    simpa using hcosh
  have hmul := h.mul_left (2 / ((u : ℝ) : ℂ))
  have hval : wickProfileTest z u
      = 2 / ((u : ℝ) : ℂ) * (Complex.cosh (z * (u : ℂ)) - 1) := by
    rw [wickProfileTest, if_neg hu]
    field_simp
  have hfun : (fun n : ℕ => wickProfileSeries z n u)
      = fun n : ℕ => 2 / ((u : ℝ) : ℂ) *
        ((z * (u : ℂ)) ^ (2 * (n + 1)) / (((2 * (n + 1)).factorial : ℕ) : ℂ)) := by
    funext n
    rw [wickProfileSeries, mul_pow]
    field_simp
    ring
  rw [hfun, hval]
  exact hmul

theorem integral_wickProfileSeries (z : ℂ) (n : ℕ) :
    ∫ u in (0 : ℝ)..1, wickProfileSeries z n u
      = z ^ (2 * (n + 1)) / (((n + 1 : ℕ) : ℂ) * (((2 * (n + 1)).factorial : ℕ) : ℂ)) := by
  have hpow : ∫ u in (0 : ℝ)..1, ((u : ℂ)) ^ (2 * n + 1)
      = ((1 : ℂ) / ((2 * n + 2 : ℕ) : ℂ)) := by
    have hcast : ∀ u : ℝ, ((u : ℂ)) ^ (2 * n + 1) = ((u ^ (2 * n + 1) : ℝ) : ℂ) := by
      intro u
      push_cast
      ring
    rw [intervalIntegral.integral_congr (g := fun u : ℝ => ((u ^ (2 * n + 1) : ℝ) : ℂ))
      (fun u _ => hcast u), intervalIntegral.integral_ofReal, integral_pow]
    push_cast
    ring
  have hconst : ∫ u in (0 : ℝ)..1, wickProfileSeries z n u
      = (2 * z ^ (2 * (n + 1)) / (((2 * (n + 1)).factorial : ℕ) : ℂ)) *
        ∫ u in (0 : ℝ)..1, ((u : ℂ)) ^ (2 * n + 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [wickProfileSeries]
    ring
  rw [hconst, hpow]
  have hfac : (((2 * (n + 1)).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have h2n : ((2 * n + 2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : 2 * n + 2 ≠ 0)
  field_simp
  push_cast
  ring

/-- **The Wick profile power series `(11)`.**  `Φ(z) = ∑_{k ≥ 1} z^{2k} / (k (2k)!)`. -/
theorem hasSum_wickProfile (z : ℂ) :
    HasSum (fun n : ℕ => z ^ (2 * (n + 1)) /
      (((n + 1 : ℕ) : ℂ) * (((2 * (n + 1)).factorial : ℕ) : ℂ))) (wickProfile z) := by
  classical
  set bound : ℕ → ℝ → ℝ := fun n _ =>
    2 * ‖z‖ ^ (2 * (n + 1)) / (((2 * (n + 1)).factorial : ℕ) : ℝ) with hbound
  have hsummableBound : Summable fun n : ℕ => bound n 0 := by
    have hbase : Summable fun m : ℕ => ‖z‖ ^ m / (m.factorial : ℝ) :=
      Real.summable_pow_div_factorial ‖z‖
    have hinj : Function.Injective fun n : ℕ => 2 * (n + 1) := by
      intro a b hab
      simp only at hab
      omega
    have hcomp := hbase.comp_injective hinj
    simpa [hbound, Function.comp_def, mul_div_assoc] using hcomp.mul_left 2
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (wickProfileSeries z n)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    intro n
    refine Continuous.aestronglyMeasurable ?_
    unfold wickProfileSeries
    fun_prop
  have hdom : ∀ n : ℕ, ∀ᵐ u : ℝ, u ∈ Set.uIoc (0 : ℝ) 1 →
      ‖wickProfileSeries z n u‖ ≤ bound n u := by
    intro n
    filter_upwards with u hu
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    have hu0 : 0 < u := hu.1
    have hu1 : u ≤ 1 := hu.2
    rw [wickProfileSeries, hbound]
    rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hu0, Complex.norm_natCast, Complex.norm_ofNat]
    have hle : u ^ (2 * n + 1) ≤ 1 := pow_le_one₀ hu0.le hu1
    have hfacpos : (0 : ℝ) < (((2 * (n + 1)).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    rw [div_le_div_iff_of_pos_right hfacpos]
    calc 2 * ‖z‖ ^ (2 * (n + 1)) * u ^ (2 * n + 1)
        ≤ 2 * ‖z‖ ^ (2 * (n + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 2 * ‖z‖ ^ (2 * (n + 1)) := by ring
  have hsum : ∀ᵐ u : ℝ, u ∈ Set.uIoc (0 : ℝ) 1 → Summable fun n => bound n u := by
    filter_upwards with u _
    exact hsummableBound
  have hint : IntervalIntegrable (fun u => ∑' n : ℕ, bound n u) MeasureTheory.volume 0 1 := by
    have : (fun u : ℝ => ∑' n : ℕ, bound n u) = fun _ : ℝ => ∑' n : ℕ, bound n 0 := by
      funext u
      rfl
    rw [this]
    exact intervalIntegrable_const
  have hpt : ∀ᵐ u : ℝ, u ∈ Set.uIoc (0 : ℝ) 1 →
      HasSum (fun n => wickProfileSeries z n u) (wickProfileTest z u) := by
    filter_upwards with u hu
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    exact hasSum_wickProfileSeries hu.1.ne'
  have hmain := intervalIntegral.hasSum_integral_of_dominated_convergence
    bound hmeas hdom hsum hint hpt
  rw [wickProfile]
  exact hmain.congr_fun fun n => (integral_wickProfileSeries z n).symm

end RHTower
