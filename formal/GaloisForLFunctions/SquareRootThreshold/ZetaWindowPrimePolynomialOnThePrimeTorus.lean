import GaloisForLFunctions.SquareRootThreshold.ZetaWindowPrimePolynomialReadsZeroCountRemainder
import GaloisForLFunctions.RHTower.FiniteEulerProductKroneckerWeylLimitLaw
import GaloisForLFunctions.RHTower.FreeLagSymbolBoundaryLayer

/-!
# The window prime polynomial on the prime torus

The real part of the window prime polynomial is a cosine polynomial over the prime powers
(`windowPrime_eq_sum`):

`Re Π_ℓ(T) = Σ_{2 ≤ n ≤ e^{2ℓ}} a_n cos(T log n)`,  `a_n = 2 Λ(n) n^{−1/2} K_ℓ(log n) ≥ 0`.

It is the value at the prime phases `ω_p = p^{−iT}` of the continuous function
`F_ℓ(ω) = Σ_n a_n Re ω_p^k` (`n = p^k`) on the prime torus
(`windowPhaseObservable_circlePhaseFlow`).

* **Aligned phases.**  `F_ℓ(1) = Σ_n a_n`.  The terms with `n ≤ e^{ℓ/2}` carry
  `K_ℓ(log n) ≥ ℓϑ²/2`, and `Σ_{n≤x} Λ(n)/√n ~ 2√x`, so `F_ℓ(1) ≥ ℓϑ² e^{ℓ/4}` for large `ℓ`; in
  particular `F_ℓ(1)` beats every multiple of `ℓ²` (`eventually_mul_sq_lt_windowPhaseObservable_one`).
* **Visiting.**  For `G < F_ℓ(1)` the function `min(1, (F_ℓ − G)⁺)` is continuous with positive
  Haar mean `I`, so by the Kronecker–Weyl law for the prime phase flow the heights
  `T ∈ [U/4, U/2]` with `Re Π_ℓ(T) > G` have measure `≥ IU/16` for all large `U`
  (`exists_eventually_volume_windowPrime_gt`).
-/

open Complex MeasureTheory Real Set Filter Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.Littlewood

/-! ### The cosine polynomial -/

/-- The weights `a_n = 2 Λ(n) n^{−1/2} K_ℓ(log n)`. -/
def primePowerWindowWeight (ℓ : ℝ) (n : ℕ) : ℝ :=
  2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * bumpKernelReal ℓ (Real.log n)

theorem primePowerWindowWeight_nonneg (ℓ : ℝ) (n : ℕ) : 0 ≤ primePowerWindowWeight ℓ n :=
  mul_nonneg (mul_nonneg zero_le_two
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)))
    (bumpKernelReal_nonneg _ _)

theorem re_ofReal_mul_ofReal_mul_exp (a b θ : ℝ) :
    ((a : ℂ) * (b : ℂ) * cexp ((θ : ℂ) * I)).re = a * b * Real.cos θ := by
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **The window prime polynomial is a cosine polynomial.** -/
theorem windowPrime_eq_sum (ℓ T : ℝ) :
    windowPrime ℓ T = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * ℓ)⌋₊,
      primePowerWindowWeight ℓ n * Real.cos (T * Real.log n) := by
  rw [windowPrime, primePolynomial, expSum, Finset.sum_product, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Fintype.sum_bool, Complex.add_re]
  have he : ∀ x : ℝ, cexp (2 * π * I * (heightWindowShift T : ℂ) * (x : ℂ)) =
      cexp (((-T * x : ℝ) : ℂ) * I) := by
    intro x
    congr 1
    have h2 : ((2 * π * heightWindowShift T : ℝ) : ℂ) = ((-T : ℝ) : ℂ) := by
      rw [two_pi_mul_windowShift]
    push_cast at h2
    rw [show (2 : ℂ) * π * I * heightWindowShift T * x = (2 * π * heightWindowShift T) * x * I by
      ring, h2]
    push_cast; ring
  simp only [primeCoeff, primeFreq, if_true, Bool.false_eq_true, if_false]
  rw [he, he, show EF.weilTest (cb ℓ 0) (cb ℓ 0) = bumpKernel ℓ from rfl, bumpKernel_eq,
    bumpKernel_eq, re_ofReal_mul_ofReal_mul_exp, re_ofReal_mul_ofReal_mul_exp,
    bumpKernelReal_neg, primePowerWindowWeight, mul_neg, neg_mul, neg_neg, Real.cos_neg]
  ring

/-! ### The lift to the prime torus -/

/-- The phase `ω_p^k` of `n = p^k`, `p` the least prime factor of `n` and `k = v_p(n)`. -/
def primePowerPhase (n : ℕ) (ω : Nat.Primes → Circle) : ℂ :=
  if h : n.minFac.Prime then ((ω (⟨n.minFac, h⟩ : Nat.Primes) : Circle) : ℂ) ^ n.factorization n.minFac
  else 1

theorem continuous_primePowerPhase (n : ℕ) : Continuous (primePowerPhase n) := by
  unfold primePowerPhase
  split_ifs with h
  · exact (continuous_subtype_val.comp (continuous_apply _)).pow _
  · exact continuous_const

theorem primePowerPhase_one (n : ℕ) : primePowerPhase n 1 = 1 := by
  unfold primePowerPhase
  split_ifs
  · exact (congrArg (· ^ n.factorization n.minFac) Circle.coe_one).trans (one_pow _)
  · rfl

/-- Along the prime phase flow the phase of a prime power `n` is `n^{−iT}`. -/
theorem re_primePowerPhase_circlePhaseFlow {n : ℕ} (hn : IsPrimePow n) (T : ℝ) :
    (primePowerPhase n (circlePhaseFlow primeFrequency T)).re = Real.cos (T * Real.log n) := by
  have hp := Nat.minFac_prime hn.ne_one
  have hpow := hn.minFac_pow_factorization_eq
  have hlog : Real.log n = (n.factorization n.minFac : ℝ) * Real.log n.minFac := by
    have h : (n : ℝ) = (n.minFac : ℝ) ^ n.factorization n.minFac := by exact_mod_cast hpow.symm
    rw [h, Real.log_pow]
  unfold primePowerPhase
  rw [dif_pos hp, HTGeometry.circlePhaseFlow_coe, ← Complex.exp_nat_mul,
    show ((n.factorization n.minFac : ℕ) : ℂ) * (((T * primeFrequency ⟨n.minFac, hp⟩ : ℝ) : ℂ) * I)
      = ((-(T * Real.log n) : ℝ) : ℂ) * I by
        rw [hlog, primeFrequency]; push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The window prime polynomial as a function of the prime phases. -/
def windowPhaseObservable (ℓ : ℝ) (ω : Nat.Primes → Circle) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * ℓ)⌋₊, primePowerWindowWeight ℓ n * (primePowerPhase n ω).re

theorem continuous_windowPhaseObservable (ℓ : ℝ) : Continuous (windowPhaseObservable ℓ) :=
  continuous_finsetSum _ fun n _ =>
    continuous_const.mul (Complex.continuous_re.comp (continuous_primePowerPhase n))

theorem windowPhaseObservable_circlePhaseFlow (ℓ T : ℝ) :
    windowPhaseObservable ℓ (circlePhaseFlow primeFrequency T) = windowPrime ℓ T := by
  rw [windowPrime_eq_sum, windowPhaseObservable]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [primePowerWindowWeight, hΛ]
  · rw [re_primePowerPhase_circlePhaseFlow (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)]

theorem windowPhaseObservable_one (ℓ : ℝ) :
    windowPhaseObservable ℓ 1 = ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * ℓ)⌋₊, primePowerWindowWeight ℓ n := by
  simp [windowPhaseObservable, primePowerPhase_one]

/-! ### The aligned value -/

/-- Short prime powers carry the full window: `F_ℓ(1) ≥ ℓϑ² Σ_{n≤e^{ℓ/2}} Λ(n)/√n`. -/
theorem windowPhaseObservable_one_ge {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ℓ * Real.smoothTransition (7 / 16) ^ 2 *
        ∑ n ∈ Finset.Icc 0 ⌊Real.exp (ℓ / 2)⌋₊, ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
      windowPhaseObservable ℓ 1 := by
  set c := Real.smoothTransition (7 / 16) ^ 2 with hc
  have hc0 : 0 ≤ c := sq_nonneg _
  rw [windowPhaseObservable_one]
  -- the terms `n = 0, 1` vanish
  have h01 : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * ℓ)⌋₊, primePowerWindowWeight ℓ n =
      ∑ n ∈ Finset.Icc 0 ⌊Real.exp (2 * ℓ)⌋₊, primePowerWindowWeight ℓ n := by
    refine Finset.sum_subset (fun n hn => ?_) fun n hn hn' => ?_
    · rw [Finset.mem_Icc] at hn ⊢; exact ⟨Nat.zero_le _, hn.2⟩
    · have : n = 0 ∨ n = 1 := by
        rw [Finset.mem_Icc] at hn hn'; omega
      rcases this with rfl | rfl <;> simp [primePowerWindowWeight]
  have hsub : Finset.Icc 0 ⌊Real.exp (ℓ / 2)⌋₊ ⊆ Finset.Icc 0 ⌊Real.exp (2 * ℓ)⌋₊ := by
    refine Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor ?_)
    exact Real.exp_le_exp.mpr (by linarith)
  rw [h01, Finset.mul_sum]
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
    primePowerWindowWeight_nonneg ℓ n)
  refine Finset.sum_le_sum fun n hn => ?_
  have hn' : (n : ℝ) ≤ Real.exp (ℓ / 2) := by
    rw [Finset.mem_Icc] at hn
    exact (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (Real.exp_pos _).le)
  have hlog : |Real.log n| ≤ ℓ / 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp; linarith
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      rw [abs_of_nonneg (Real.log_nonneg h1)]
      calc Real.log n ≤ Real.log (Real.exp (ℓ / 2)) := Real.log_le_log (by linarith) hn'
        _ = ℓ / 2 := Real.log_exp _
  have hK := bumpKernelReal_ge hℓ hlog
  have ha : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [primePowerWindowWeight]
  calc ℓ * c * (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
      = 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (ℓ / 2 * c) := by ring
    _ ≤ 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * bumpKernelReal ℓ (Real.log n) :=
        mul_le_mul_of_nonneg_left hK (by positivity)

/-- **The aligned value beats every multiple of `ℓ²`.** -/
theorem eventually_mul_sq_lt_windowPhaseObservable_one (M : ℝ) :
    ∀ᶠ ℓ in atTop, M * ℓ ^ 2 < windowPhaseObservable ℓ 1 := by
  set c := Real.smoothTransition (7 / 16) ^ 2 with hc
  have hc0 : 0 < c := pow_pos (Real.smoothTransition.pos_of_pos (by norm_num)) 2
  -- `Σ_{n ≤ x} Λ(n)/√n ≥ √x` for large `x`
  have hsum : ∀ᶠ x : ℝ in atTop, Real.sqrt x ≤
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
    filter_upwards [FreeLagTrace.tendsto_sum_vonMangoldt_div_sqrt.eventually (lt_mem_nhds
      (by norm_num : (1 : ℝ) < 2)), eventually_gt_atTop 0] with x hx hx0
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    rw [lt_div_iff₀ hs, one_mul] at hx
    exact hx.le
  have hexp : Tendsto (fun ℓ : ℝ => Real.exp (ℓ / 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
  -- `e^{ℓ/4}/(ℓ/4) → ∞`
  have hgrow : Tendsto (fun ℓ : ℝ => Real.exp (ℓ / 4) / (ℓ / 4) ^ 1) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 1).comp (tendsto_id.atTop_div_const (by norm_num))
  filter_upwards [hexp.eventually hsum, hgrow.eventually_gt_atTop (4 * |M| / c),
    eventually_gt_atTop 0] with ℓ h1 h2 hℓ
  have hsq : Real.sqrt (Real.exp (ℓ / 2)) = Real.exp (ℓ / 4) := by
    rw [show ℓ / 2 = ℓ / 4 + ℓ / 4 by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [hsq] at h1
  rw [pow_one, div_lt_div_iff₀ hc0 (by positivity)] at h2
  have hge := windowPhaseObservable_one_ge hℓ
  rw [← hc] at hge
  have hM : M * ℓ ^ 2 ≤ |M| * ℓ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
  calc M * ℓ ^ 2 ≤ |M| * ℓ ^ 2 := hM
    _ < ℓ * c * Real.exp (ℓ / 4) := by nlinarith [abs_nonneg M]
    _ ≤ ℓ * c * ∑ n ∈ Finset.Icc 0 ⌊Real.exp (ℓ / 2)⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ windowPhaseObservable ℓ 1 := hge

/-! ### Visiting the superlevel sets in every window -/

/-- **Kronecker visits in windows.**  For `G < F_ℓ(1)` there is `c > 0` such that for all large `U`
the heights `T ∈ [U/4, U/2]` with `Re Π_ℓ(T) > G` have measure at least `cU`. -/
theorem exists_eventually_volume_windowPrime_gt {ℓ G : ℝ} (hG : G < windowPhaseObservable ℓ 1) :
    ∃ c > 0, ∀ᶠ U in atTop, ENNReal.ofReal (c * U) ≤
      volume ({T | G < windowPrime ℓ T} ∩ Icc (U / 4) (U / 2)) := by
  set F := windowPhaseObservable ℓ with hF
  have hFc : Continuous F := continuous_windowPhaseObservable ℓ
  -- the observable `ψ = min(1, (F − G)⁺)`
  let ψ : C((Nat.Primes → Circle), ℝ) :=
    ⟨fun ω => min 1 (max 0 (F ω - G)), continuous_const.min (continuous_const.max
      (hFc.sub continuous_const))⟩
  have hψ1 : ∀ ω, ψ ω ≤ 1 := fun ω => min_le_left _ _
  have hψ0 : ∀ ω, 0 ≤ ψ ω := fun ω => le_min zero_le_one (le_max_left _ _)
  have hψG : ∀ ω, F ω ≤ G → ψ ω = 0 := fun ω h => by
    show min 1 (max 0 (F ω - G)) = 0
    rw [max_eq_left (by linarith), min_eq_right zero_le_one]
  set Φ := unitTorusHomeomorphCircles Nat.Primes
  set I := ∫ x, ψ (Φ x) ∂(torusHaar Nat.Primes) with hI
  have hI0 : 0 < I := by
    refine (ψ.continuous.comp Φ.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun x => hψ0 _) (x := Φ.symm 1) ?_
    simp only [Homeomorph.apply_symm_apply]
    show min 1 (max 0 (F 1 - G)) ≠ 0
    rw [max_eq_right (by linarith)]
    exact (lt_min one_pos (by linarith)).ne'
  have hlim := tendsto_windowAverage_primeFlow_real ψ
  rw [← hI] at hlim
  have hev := hlim.eventually (Ioo_mem_nhds (by linarith : 3 * I / 4 < I) (by linarith : I < 5 * I / 4))
  refine ⟨I / 16, by positivity, ?_⟩
  have h2 : Tendsto (fun U : ℝ => U / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have h4 : Tendsto (fun U : ℝ => U / 4) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  filter_upwards [h2.eventually hev, h4.eventually hev, eventually_gt_atTop 0] with U hU2 hU4 hU0
  set g : ℝ → ℝ := fun τ => ψ (circlePhaseFlow primeFrequency τ) with hg
  have hgc : Continuous g := ψ.continuous.comp (continuous_circlePhaseFlow _)
  set V := {T | G < windowPrime ℓ T} with hV
  have hVo : IsOpen V := by
    have : V = (fun T => windowPhaseObservable ℓ (circlePhaseFlow primeFrequency T)) ⁻¹' Ioi G := by
      ext T; simp [hV, windowPhaseObservable_circlePhaseFlow]
    rw [this]
    exact isOpen_Ioi.preimage (hFc.comp (continuous_circlePhaseFlow _))
  -- the window integral of `g`
  have hJ2 : U / 2 * (3 * I / 4) < ∫ τ in (0 : ℝ)..(U / 2), g τ := by
    have := mul_lt_mul_of_pos_left hU2.1 (by positivity : 0 < U / 2)
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
  have hJ4 : ∫ τ in (0 : ℝ)..(U / 4), g τ < U / 4 * (5 * I / 4) := by
    have := mul_lt_mul_of_pos_left hU4.2 (by positivity : 0 < U / 4)
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
  have hwin : ∫ τ in (U / 4)..(U / 2), g τ =
      (∫ τ in (0 : ℝ)..(U / 2), g τ) - ∫ τ in (0 : ℝ)..(U / 4), g τ :=
    (intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)).symm
  have hlow : I / 16 * U < ∫ τ in (U / 4)..(U / 2), g τ := by rw [hwin]; linarith
  -- `g ≤ 1_V`
  have hle : ∫ τ in (U / 4)..(U / 2), g τ ≤
      ∫ τ in (U / 4)..(U / 2), V.indicator (fun _ => (1 : ℝ)) τ := by
    refine intervalIntegral.integral_mono_on (by linarith) (hgc.intervalIntegrable _ _) ?_
      fun τ _ => ?_
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
      exact (integrableOn_const (by simp) (by simp)).indicator hVo.measurableSet
    · by_cases hτ : τ ∈ V
      · rw [indicator_of_mem hτ]; exact hψ1 _
      · rw [indicator_of_notMem hτ]
        refine (hψG _ ?_).le
        rw [hF, windowPhaseObservable_circlePhaseFlow]
        exact not_lt.mp hτ
  have hind : ∫ τ in (U / 4)..(U / 2), V.indicator (fun _ => (1 : ℝ)) τ =
      (volume (V ∩ Ioc (U / 4) (U / 2))).toReal := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_indicator hVo.measurableSet,
      setIntegral_const, measureReal_def, Measure.restrict_apply hVo.measurableSet, smul_eq_mul,
      mul_one]
  have hmono : volume (V ∩ Ioc (U / 4) (U / 2)) ≤ volume (V ∩ Icc (U / 4) (U / 2)) :=
    measure_mono (inter_subset_inter_right _ Ioc_subset_Icc_self)
  refine ENNReal.ofReal_le_of_le_toReal ?_
  calc I / 16 * U ≤ (volume (V ∩ Ioc (U / 4) (U / 2))).toReal := by linarith
    _ ≤ (volume (V ∩ Icc (U / 4) (U / 2))).toReal :=
        ENNReal.toReal_mono ((measure_mono inter_subset_right).trans_lt measure_Icc_lt_top).ne
          hmono

end GaloisForLFunctions.SquareRootThreshold
