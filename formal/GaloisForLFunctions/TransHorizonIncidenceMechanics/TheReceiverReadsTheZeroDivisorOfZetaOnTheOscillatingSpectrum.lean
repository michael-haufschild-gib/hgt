import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheLogTwistedOscillatingSmoothPowerIsPaidExactlyAtTheDoubleZerosOfZeta

/-!
# The receiver reads the zero divisor of ζ on the oscillating spectrum

Fix `0 < ε ≤ 1/2`. For a finite set `J` of positive frequencies and complex coefficients
`p(t, k)`, `k ≤ K`, let
`c(d) = Σ_{t ∈ J} Σ_{k ≤ K} Re(p(t, k) d^{ρ_t − 1} (log d)^k)`, `ρ_t = 1 − ε + it`.
Its receiver is bounded **if and only if**, at every frequency `t ∈ J`, `ζ` vanishes at `ρ_t` to order
greater than the log-degree of `p(t, ·)`
(`receiverBounded_oscillatingLogPolynomial_iff`). Different frequencies do not interact, and at each
frequency the paid log-polynomials are exactly those of degree below the multiplicity of `ρ_t`.
In particular `d^{-ε} cos(t log d) (log d)^k` is paid iff `ζ^{(i)}(ρ_t) = 0` for all `i ≤ k`
(`receiverBounded_logPowerOscillation_iff`): the receiver reads the complete zero divisor of `ζ` in
`1/2 ≤ Re s < 1`, multiplicities included.

* **Taylor expansion of the floor sum in the exponent.** With `R_n(ρ) = D_ρ(n) − ζ(2 − ρ)n − ζ(ρ)n^ρ/ρ`,
  `Σ_{d ≤ n} d^{ρ−1}(log d)^k ⌊n/d⌋ − L_k(2 − ρ) n = ∂^k R_n(ρ) + Σ_{i ≤ k} C(k,i) f^{(i)}(ρ) n^ρ (log n)^{k−i}`,
  `f = ζ/id`, `L_k(s) = Σ (log d)^k d^{-s}` (`sum_logPower_floor_sub_eq`); Cauchy's estimate bounds
  `∂^k R_n(ρ)` by `k! K (√n)^{1−ε/2} (2/ε)^k`.
* **The main term** is `n^{1−ε} Σ_m (log n)^m Re(Σ_t q(t, m) n^{it})` with a triangular coefficient
  matrix `q(t, m) = Σ_{k ≥ m} p(t, k) C(k, m) f_t^{(k−m)}` (`sum_re_mul_leibniz_eq`); `q(t, ·) = 0`
  iff `f_t`, equivalently `ζ`, vanishes to order above the degree (`forall_mainCoeff_eq_zero_iff`).
* **Energy of the main term.** A paid receiver bounds `Σ_{n ≤ T} u(n)²/n`; on the windows
  `N < n ≤ N²` the top log-power amplifies the energy of its oscillation, which is
  `(Σ_t |q(t, m)|²/2) log N − O(1)` because the cross frequencies `t ± s ≠ 0` have bounded harmonic
  sums. Descending in the degree forces every coefficient to vanish.
-/

open Finset Filter Topology Complex Metric
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Iterated derivatives of the floor-sum decomposition -/

/-- `∂^k_ρ D_ρ(n) = Σ_{d ≤ n} d^{ρ−1} (log d)^k ⌊n/d⌋`. -/
theorem iteratedDeriv_cpowFloorSum (n k : ℕ) :
    iteratedDeriv k (fun ρ : ℂ => cpowFloorSum ρ n) = fun ρ =>
      ∑ d ∈ Icc 1 n, ((d : ℝ) : ℂ) ^ (ρ - 1) * ((Real.log d : ℂ) ^ k * ((n / d : ℕ) : ℂ)) := by
  induction k with
  | zero =>
    rw [iteratedDeriv_zero]
    funext ρ
    simp only [cpowFloorSum, pow_zero, one_mul]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext ρ
    refine (HasDerivAt.fun_sum fun d hd => ?_).deriv
    have hd0 : ((d : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      exact_mod_cast this.ne'
    have h1 : HasDerivAt (fun ρ : ℂ => ((d : ℝ) : ℂ) ^ (ρ - 1))
        (((d : ℝ) : ℂ) ^ (ρ - 1) * (Real.log d : ℂ)) ρ := by
      have h := ((hasDerivAt_id ρ).sub_const 1).const_cpow (c := ((d : ℝ) : ℂ)) (Or.inl hd0)
      rw [← Complex.ofReal_log (Nat.cast_nonneg d)] at h
      simpa only [id, mul_one] using h
    exact (h1.mul_const ((Real.log d : ℂ) ^ k * ((n / d : ℕ) : ℂ))).congr_deriv (by ring)

/-- `∂^k_ρ x^ρ = x^ρ (log x)^k` for `x > 0`. -/
theorem iteratedDeriv_ofReal_cpow {x : ℝ} (hx : 0 < x) (k : ℕ) :
    iteratedDeriv k (fun ρ : ℂ => ((x : ℝ) : ℂ) ^ ρ) = fun ρ =>
      ((x : ℝ) : ℂ) ^ ρ * (Real.log x : ℂ) ^ k := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  induction k with
  | zero => rw [iteratedDeriv_zero]; funext ρ; simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext ρ
    have h := (hasDerivAt_id ρ).const_cpow (c := ((x : ℝ) : ℂ)) (Or.inl hx0)
    rw [← Complex.ofReal_log hx.le] at h
    exact ((h.mul_const ((Real.log x : ℂ) ^ k)).congr_deriv (by simp only [id]; ring)).deriv

/-- `ζ/id` is smooth away from `0` and `1`. -/
theorem contDiffAt_zeta_div {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (k : ℕ) :
    ContDiffAt ℂ k (fun s : ℂ => riemannZeta s / s) ρ := by
  have hU : ({0}ᶜ ∩ {1}ᶜ : Set ℂ) ∈ 𝓝 ρ :=
    (isOpen_compl_singleton.inter isOpen_compl_singleton).mem_nhds ⟨h0, h1⟩
  refine (DifferentiableOn.analyticAt (fun s hs => ?_) hU).contDiffAt
  exact ((differentiableAt_riemannZeta hs.2).div differentiableAt_id hs.1).differentiableWithinAt

/-- `(log^k · 1)(n) = (log n)^k`. -/
theorem logMul_iterate_one_apply (k n : ℕ) :
    (LSeries.logMul^[k] 1) n = Complex.log n ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ, mul_comm]

/-- On `Re s > 1`, `ζ^{(k)}(s) = (−1)^k Σ (log d)^k d^{-s}`. -/
theorem iteratedDeriv_riemannZeta_eq {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    iteratedDeriv k riemannZeta s = (-1) ^ k * LSeries (LSeries.logMul^[k] 1) s := by
  have habs : LSeries.abscissaOfAbsConv 1 < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  rw [← LSeries_iteratedDeriv k habs]
  refine Filter.EventuallyEq.iteratedDeriv_eq k ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  exact (LSeries_one_eq_riemannZeta hz).symm

/-! ### Log-power oscillations -/

/-- The log-power oscillation `d^{ρ−1} (log d)^k`, `ρ = 1 − ε + it`. -/
def logPowerOscillation (ε t : ℝ) (k d : ℕ) : ℂ :=
  ((d : ℝ) : ℂ) ^ (oscillationExponent ε t - 1) * (Real.log d : ℂ) ^ k

/-- The mean of a log-power oscillation is `L_k(2 − ρ) = Σ (log d)^k d^{ρ−2}`. -/
theorem hasSum_logPowerOscillation_div {ε : ℝ} (hε : 0 < ε) (t : ℝ) (k : ℕ) :
    HasSum (fun d : ℕ => logPowerOscillation ε t k d / d)
      (LSeries (LSeries.logMul^[k] 1) (2 - oscillationExponent ε t)) := by
  set ρ := oscillationExponent ε t with hρ
  set s : ℂ := 2 - ρ with hs
  have hre : 1 < s.re := by rw [hs, sub_re, oscillationExponent_re]; norm_num; linarith
  have habs : LSeries.abscissaOfAbsConv (LSeries.logMul^[k] 1) < s.re := by
    rw [LSeries.absicssaOfAbsConv_logPowMul, LSeries.abscissaOfAbsConv_one]; exact_mod_cast hre
  refine (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum.congr_fun fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have h1 : (Real.log d : ℂ) ^ k / (d : ℂ) ^ s =
      ((d : ℝ) : ℂ) ^ (ρ - 1) * (Real.log d : ℂ) ^ k / ((d : ℝ) : ℂ) := by
    rw [show (d : ℂ) = ((d : ℝ) : ℂ) by push_cast; rfl, hs, div_eq_mul_inv, ← Complex.cpow_neg,
      show -(2 - ρ) = ρ - 1 - 1 by ring, Complex.cpow_sub _ _ hdC, Complex.cpow_one]
    ring
  rw [LSeries.term_of_ne_zero hd.ne', logMul_iterate_one_apply, ← Complex.natCast_log, h1,
    logPowerOscillation, ← hρ]
  simp only [Complex.ofReal_natCast]

/-- **The `k`-th log-twisted floor sum.** With `ρ = 1 − ε + it` and `f = ζ/id`,
`Σ_{d ≤ n} d^{ρ−1}(log d)^k ⌊n/d⌋ − L_k(2 − ρ) n = ∂^k R_n(ρ) + Σ_{i ≤ k} C(k,i) f^{(i)}(ρ) n^ρ (log n)^{k−i}`. -/
theorem sum_logPower_floor_sub_eq {ε t : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) :
    ∑ d ∈ Icc 1 n, logPowerOscillation ε t k d * ((n / d : ℕ) : ℂ) -
        LSeries (LSeries.logMul^[k] 1) (2 - oscillationExponent ε t) * n =
      iteratedDeriv k (floorRemainder n) (oscillationExponent ε t) +
        ∑ i ∈ range (k + 1), (k.choose i : ℂ) *
          iteratedDeriv i (fun s : ℂ => riemannZeta s / s) (oscillationExponent ε t) *
          (((n : ℝ) : ℂ) ^ oscillationExponent ε t * (Real.log n : ℂ) ^ (k - i)) := by
  set ρ := oscillationExponent ε t with hρ
  have hre : ρ.re = 1 - ε := oscillationExponent_re ε t
  have h0 : ρ ≠ 0 := fun h => by rw [h, zero_re] at hre; linarith
  have h1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hre; linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- regularity of the three pieces
  have hD : ContDiffAt ℂ k (fun ρ : ℂ => cpowFloorSum ρ n) ρ :=
    (Differentiable.analyticAt (fun ρ => (hasDerivAt_cpowFloorSum n ρ).differentiableAt)
      ρ).contDiffAt
  have hZ : ContDiffAt ℂ k (fun ρ : ℂ => riemannZeta (2 - ρ) * n) ρ := by
    refine (DifferentiableOn.analyticAt (fun s hs => ?_)
      (isOpen_compl_singleton.mem_nhds h1)).contDiffAt
    exact ((hasDerivAt_zeta_two_sub hs).differentiableAt.mul_const _).differentiableWithinAt
  have hf : ContDiffAt ℂ k (fun s : ℂ => riemannZeta s / s) ρ := contDiffAt_zeta_div h0 h1 k
  have hg : ContDiffAt ℂ k (fun s : ℂ => ((n : ℝ) : ℂ) ^ s) ρ :=
    (Differentiable.analyticAt (fun s => differentiableAt_id.const_cpow
      (Or.inl (by exact_mod_cast hn0.ne'))) ρ).contDiffAt
  have hR : floorRemainder n = ((fun ρ : ℂ => cpowFloorSum ρ n) -
      fun ρ : ℂ => riemannZeta (2 - ρ) * n) -
      (fun s : ℂ => riemannZeta s / s) * (fun s : ℂ => ((n : ℝ) : ℂ) ^ s) := by
    funext s
    simp only [floorRemainder, Pi.sub_apply, Pi.mul_apply]
    ring
  -- the iterated derivatives of the pieces
  have eD : iteratedDeriv k (fun ρ : ℂ => cpowFloorSum ρ n) ρ =
      ∑ d ∈ Icc 1 n, ((d : ℝ) : ℂ) ^ (ρ - 1) * ((Real.log d : ℂ) ^ k * ((n / d : ℕ) : ℂ)) :=
    congrFun (iteratedDeriv_cpowFloorSum n k) ρ
  have hs2 : 1 < (2 - ρ).re := by rw [sub_re, hre]; norm_num; linarith
  have eZ : iteratedDeriv k (fun ρ : ℂ => riemannZeta (2 - ρ) * n) ρ =
      LSeries (LSeries.logMul^[k] 1) (2 - ρ) * n := by
    have e1 : iteratedDeriv k (fun x : ℂ => riemannZeta (2 - x) * n) ρ =
        iteratedDeriv k (fun x : ℂ => riemannZeta (2 - x)) ρ * n :=
      iteratedDeriv_mul_const_field (fun x : ℂ => riemannZeta (2 - x)) (n : ℂ)
    have e2 : iteratedDeriv k (fun z : ℂ => riemannZeta (2 - z)) ρ =
        (-1 : ℂ) ^ k • iteratedDeriv k riemannZeta (2 - ρ) :=
      congrFun (iteratedDeriv_comp_const_sub k riemannZeta 2) ρ
    rw [e1, e2, iteratedDeriv_riemannZeta_eq hs2, smul_eq_mul, ← mul_assoc, ← mul_pow]
    norm_num
  have eM : iteratedDeriv k ((fun s : ℂ => riemannZeta s / s) * fun s : ℂ => ((n : ℝ) : ℂ) ^ s) ρ =
      ∑ i ∈ range (k + 1), (k.choose i : ℂ) * iteratedDeriv i (fun s : ℂ => riemannZeta s / s) ρ *
        (((n : ℝ) : ℂ) ^ ρ * (Real.log n : ℂ) ^ (k - i)) := by
    rw [iteratedDeriv_mul hf hg]
    refine sum_congr rfl fun i _ => ?_
    rw [iteratedDeriv_ofReal_cpow hn0]
  have eR : iteratedDeriv k (floorRemainder n) ρ =
      iteratedDeriv k (fun ρ : ℂ => cpowFloorSum ρ n) ρ -
        iteratedDeriv k (fun ρ : ℂ => riemannZeta (2 - ρ) * n) ρ -
        iteratedDeriv k ((fun s : ℂ => riemannZeta s / s) * fun s : ℂ => ((n : ℝ) : ℂ) ^ s) ρ := by
    rw [hR, iteratedDeriv_sub (f := (fun ρ : ℂ => cpowFloorSum ρ n) -
        fun ρ : ℂ => riemannZeta (2 - ρ) * n)
      (g := (fun s : ℂ => riemannZeta s / s) * fun s : ℂ => ((n : ℝ) : ℂ) ^ s) (hD.sub hZ)
      (hf.mul hg), iteratedDeriv_sub (f := fun ρ : ℂ => cpowFloorSum ρ n)
      (g := fun ρ : ℂ => riemannZeta (2 - ρ) * n) hD hZ]
  rw [eR, eD, eZ, eM]
  simp only [logPowerOscillation]
  rw [← hρ, show ∑ d ∈ Icc 1 n, ((d : ℝ) : ℂ) ^ (ρ - 1) * (Real.log d : ℂ) ^ k * ((n / d : ℕ) : ℂ) =
      ∑ d ∈ Icc 1 n, ((d : ℝ) : ℂ) ^ (ρ - 1) * ((Real.log d : ℂ) ^ k * ((n / d : ℕ) : ℂ)) from
    sum_congr rfl fun d _ => mul_assoc _ _ _]
  ring

/-! ### The coefficient algebra -/

/-- Reindexing the Leibniz expansion by the power of `log n`. -/
theorem sum_range_mul_sum_choose_eq (K : ℕ) (p F : ℕ → ℂ) (L : ℂ) :
    ∑ k ∈ range (K + 1), p k * ∑ i ∈ range (k + 1), (k.choose i : ℂ) * F i * L ^ (k - i) =
      ∑ m ∈ range (K + 1), (∑ k ∈ range (K + 1),
        if m ≤ k then p k * (k.choose m : ℂ) * F (k - m) else 0) * L ^ m := by
  have inner : ∀ k ∈ range (K + 1),
      p k * ∑ i ∈ range (k + 1), (k.choose i : ℂ) * F i * L ^ (k - i) =
        ∑ m ∈ range (K + 1), (if m ≤ k then p k * (k.choose m : ℂ) * F (k - m) else 0) * L ^ m := by
    intro k hk
    have hkK : k + 1 ≤ K + 1 := by have := mem_range.mp hk; omega
    rw [← sum_range_add_sum_Ico _ hkK, sum_eq_zero (s := Ico (k + 1) (K + 1)) (fun m hm => ?_),
      add_zero, mul_sum]
    · rw [← sum_range_reflect (fun m => (if m ≤ k then p k * (k.choose m : ℂ) * F (k - m) else 0) *
        L ^ m)]
      refine sum_congr rfl fun j hj => ?_
      have hj' : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
      rw [Nat.add_sub_cancel, if_pos (Nat.sub_le k j), Nat.choose_symm hj', Nat.sub_sub_self hj']
      ring
    · rw [mem_Ico] at hm
      rw [if_neg (by omega), zero_mul]
  rw [sum_congr rfl inner, sum_comm]
  exact sum_congr rfl fun m _ => by rw [sum_mul]

/-- **The triangular coefficient law.** The reindexed coefficients `q(m)` all vanish iff `F`
vanishes up to the degree of `p`. -/
theorem forall_coeff_eq_zero_iff (K : ℕ) (p F : ℕ → ℂ) :
    (∀ m ≤ K, ∑ k ∈ range (K + 1),
        (if m ≤ k then p k * (k.choose m : ℂ) * F (k - m) else 0) = 0) ↔
      ∀ k ≤ K, p k ≠ 0 → ∀ i ≤ k, F i = 0 := by
  constructor
  · intro h k₀ hk₀ hp₀
    set S := (range (K + 1)).filter (fun k => p k ≠ 0) with hS
    have hk₀S : k₀ ∈ S := by rw [hS, mem_filter, mem_range]; exact ⟨by omega, hp₀⟩
    set K₀ := S.max' ⟨k₀, hk₀S⟩ with hK₀
    have hK₀S : K₀ ∈ S := S.max'_mem _
    rw [hS, mem_filter, mem_range] at hK₀S
    have hk₀K₀ : k₀ ≤ K₀ := S.le_max' k₀ hk₀S
    have hbig : ∀ k ∈ range (K + 1), K₀ < k → p k = 0 := by
      intro k hk hlt
      by_contra hpk
      have : k ∈ S := by rw [hS, mem_filter]; exact ⟨hk, hpk⟩
      exact absurd (S.le_max' k this) (by omega)
    have hF : ∀ r, r ≤ K₀ → F r = 0 := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro hr
        have hq := h (K₀ - r) (by omega)
        rw [sum_eq_single K₀ (fun b hb hbK => ?_) (fun hK => absurd (mem_range.mpr hK₀S.1) hK),
          if_pos (Nat.sub_le K₀ r), Nat.sub_sub_self hr] at hq
        · have hc : (K₀.choose (K₀ - r) : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.choose_pos (Nat.sub_le K₀ r)).ne'
          exact (mul_eq_zero.mp hq).resolve_left (mul_ne_zero hK₀S.2 hc)
        · split_ifs with hle
          · rcases lt_or_gt_of_ne hbK with hlt | hgt
            · rw [ih (b - (K₀ - r)) (by omega) (by omega), mul_zero]
            · rw [hbig b hb hgt, zero_mul, zero_mul]
          · rfl
    exact fun i hi => hF i (hi.trans hk₀K₀)
  · intro h m hm
    refine sum_eq_zero fun k hk => ?_
    split_ifs with hmk
    · by_cases hp : p k = 0
      · rw [hp, zero_mul, zero_mul]
      · rw [h k (by have := mem_range.mp hk; omega) hp (k - m) (Nat.sub_le k m), mul_zero]
    · rfl

/-- `ζ/id` and `ζ` vanish to the same order at `ρ ≠ 0, 1`. -/
theorem forall_iteratedDeriv_zeta_div_eq_zero_iff {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (k : ℕ) :
    (∀ i ≤ k, iteratedDeriv i (fun s : ℂ => riemannZeta s / s) ρ = 0) ↔
      ∀ i ≤ k, iteratedDeriv i riemannZeta ρ = 0 := by
  have hz : ∀ i : ℕ, ContDiffAt ℂ i riemannZeta ρ := fun i =>
    (DifferentiableOn.analyticAt
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt)
      (isOpen_compl_singleton.mem_nhds h1)).contDiffAt
  have hf : ∀ i : ℕ, ContDiffAt ℂ i (fun s : ℂ => riemannZeta s / s) ρ := fun i =>
    contDiffAt_zeta_div h0 h1 i
  constructor
  · intro h i hi
    have heq : riemannZeta =ᶠ[𝓝 ρ] (fun s : ℂ => riemannZeta s / s) * id := by
      filter_upwards [isOpen_compl_singleton.mem_nhds h0] with s hs
      simp only [Pi.mul_apply, id]
      rw [div_mul_cancel₀ _ hs]
    rw [heq.iteratedDeriv_eq i, iteratedDeriv_mul (hf i) contDiffAt_id]
    exact sum_eq_zero fun j hj => by
      rw [h j (by have := mem_range.mp hj; omega), mul_zero, zero_mul]
  · intro h i hi
    have heq : (fun s : ℂ => riemannZeta s / s) = riemannZeta * fun s : ℂ => s⁻¹ := by
      funext s; simp only [Pi.mul_apply, div_eq_mul_inv]
    rw [heq, iteratedDeriv_mul (hz i) (contDiffAt_inv ℂ h0)]
    exact sum_eq_zero fun j hj => by
      rw [h j (by have := mem_range.mp hj; omega), mul_zero, zero_mul]

/-! ### Oscillating log-polynomials and their prefix law -/

/-- The oscillating log-polynomial `Σ_{t ∈ J} Σ_{k ≤ K} Re(p(t,k) d^{ρ_t−1} (log d)^k)`. -/
def oscillatingLogPolynomial (ε : ℝ) (J : Finset ℝ) (K : ℕ) (p : ℝ → ℕ → ℂ) (d : ℕ) : ℝ :=
  ∑ t ∈ J, ∑ k ∈ range (K + 1), (p t k * logPowerOscillation ε t k d).re

/-- The coefficient of `(log n)^m` at frequency `t`: `q(t,m) = Σ_{k ≥ m} p(t,k) C(k,m) f_t^{(k−m)}`. -/
def mainCoeff (ε : ℝ) (K : ℕ) (p : ℝ → ℕ → ℂ) (t : ℝ) (m : ℕ) : ℂ :=
  ∑ k ∈ range (K + 1), if m ≤ k then p t k * (k.choose m : ℂ) *
    iteratedDeriv (k - m) (fun s : ℂ => riemannZeta s / s) (oscillationExponent ε t) else 0

/-- The rate of the prefix law. -/
def spectralRate (ε : ℝ) (J : Finset ℝ) (K : ℕ) (p : ℝ → ℕ → ℂ) : ℝ :=
  ∑ t ∈ J, ∑ k ∈ range (K + 1), ‖p t k‖ * (k.factorial * discRate ε t / (ε / 2) ^ k)

theorem hasSum_oscillatingLogPolynomial_div {ε : ℝ} (hε : 0 < ε) (J : Finset ℝ) (K : ℕ)
    (p : ℝ → ℕ → ℂ) :
    HasSum (fun d : ℕ => oscillatingLogPolynomial ε J K p d / d)
      (∑ t ∈ J, ∑ k ∈ range (K + 1),
        (p t k * LSeries (LSeries.logMul^[k] 1) (2 - oscillationExponent ε t)).re) := by
  have h : ∀ t k, HasSum (fun d : ℕ => (p t k * logPowerOscillation ε t k d).re / d)
      (p t k * LSeries (LSeries.logMul^[k] 1) (2 - oscillationExponent ε t)).re := by
    intro t k
    refine (Complex.hasSum_re ((hasSum_logPowerOscillation_div hε t k).mul_left (p t k))).congr_fun
      fun d => ?_
    rw [← mul_div_assoc, show (d : ℂ) = ((d : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]
  refine (hasSum_sum fun t _ => hasSum_sum fun k _ => h t k).congr_fun fun d => ?_
  rw [oscillatingLogPolynomial, sum_div]
  exact sum_congr rfl fun t _ => by rw [sum_div]

/-- The prefix of an oscillating log-polynomial, frequency by frequency and power by power. -/
theorem weightCenteredPrefix_oscillatingLogPolynomial_eq {ε : ℝ} (hε : 0 < ε) (J : Finset ℝ)
    (K : ℕ) (p : ℝ → ℕ → ℂ) (n : ℕ) :
    weightCenteredPrefix (oscillatingLogPolynomial ε J K p)
        (∑' d : ℕ, oscillatingLogPolynomial ε J K p d / d) n =
      ∑ t ∈ J, ∑ k ∈ range (K + 1), (p t k * (∑ d ∈ Icc 1 n, logPowerOscillation ε t k d *
        ((n / d : ℕ) : ℂ) - LSeries (LSeries.logMul^[k] 1) (2 - oscillationExponent ε t) * n)).re := by
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    (hasSum_oscillatingLogPolynomial_div hε J K p).tsum_eq]
  have e1 : ∀ t k, (p t k * (∑ d ∈ Icc 1 n, logPowerOscillation ε t k d * ((n / d : ℕ) : ℂ) -
      LSeries (LSeries.logMul^[k] 1) (2 - oscillationExponent ε t) * n)).re =
      ∑ d ∈ Icc 1 n, (p t k * logPowerOscillation ε t k d).re * ((n / d : ℕ) : ℝ) -
        (p t k * LSeries (LSeries.logMul^[k] 1) (2 - oscillationExponent ε t)).re * n := by
    intro t k
    rw [mul_sub, sub_re, mul_sum, Complex.re_sum]
    congr 1
    · refine sum_congr rfl fun d _ => ?_
      rw [← mul_assoc, show ((n / d : ℕ) : ℂ) = (((n / d : ℕ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.re_mul_ofReal]
    · rw [← mul_assoc, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.re_mul_ofReal]
  simp only [e1, oscillatingLogPolynomial, sum_mul, sum_sub_distrib]
  rw [sum_comm (s := Icc 1 n)]
  congr 1
  exact sum_congr rfl fun t _ => sum_comm

/-- The main term in the coordinates `(log n)^m n^{it}`. -/
theorem sum_re_mul_leibniz_eq (ε : ℝ) (J : Finset ℝ) (K : ℕ) (p : ℝ → ℕ → ℂ) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ t ∈ J, ∑ k ∈ range (K + 1), (p t k * ∑ i ∈ range (k + 1), (k.choose i : ℂ) *
        iteratedDeriv i (fun s : ℂ => riemannZeta s / s) (oscillationExponent ε t) *
        (((n : ℝ) : ℂ) ^ oscillationExponent ε t * (Real.log n : ℂ) ^ (k - i))).re =
      (n : ℝ) ^ (1 - ε) * ∑ m ∈ range (K + 1), Real.log n ^ m *
        (∑ t ∈ J, mainCoeff ε K p t m * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hper : ∀ t, ∑ k ∈ range (K + 1), (p t k * ∑ i ∈ range (k + 1), (k.choose i : ℂ) *
        iteratedDeriv i (fun s : ℂ => riemannZeta s / s) (oscillationExponent ε t) *
        (((n : ℝ) : ℂ) ^ oscillationExponent ε t * (Real.log n : ℂ) ^ (k - i))).re =
      (n : ℝ) ^ (1 - ε) * ∑ m ∈ range (K + 1), Real.log n ^ m *
        (mainCoeff ε K p t m * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re := by
    intro t
    have hsplit : ((n : ℝ) : ℂ) ^ oscillationExponent ε t =
        (((n : ℝ) ^ (1 - ε) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
      rw [oscillationExponent, Complex.cpow_add _ _ (by exact_mod_cast hn0.ne'),
        Complex.ofReal_cpow hn0.le]
    have e : ∀ k, p t k * ∑ i ∈ range (k + 1), (k.choose i : ℂ) *
        iteratedDeriv i (fun s : ℂ => riemannZeta s / s) (oscillationExponent ε t) *
        (((n : ℝ) : ℂ) ^ oscillationExponent ε t * (Real.log n : ℂ) ^ (k - i)) =
        (((n : ℝ) ^ (1 - ε) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) *
          (p t k * ∑ i ∈ range (k + 1), (k.choose i : ℂ) *
            iteratedDeriv i (fun s : ℂ => riemannZeta s / s) (oscillationExponent ε t) *
            (Real.log n : ℂ) ^ (k - i)) := by
      intro k
      rw [hsplit, mul_sum, mul_sum, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    rw [← Complex.re_sum, sum_congr rfl fun k _ => e k, ← mul_sum,
      sum_range_mul_sum_choose_eq K (p t)
        (fun i => iteratedDeriv i (fun s : ℂ => riemannZeta s / s) (oscillationExponent ε t)),
      mul_assoc, Complex.re_ofReal_mul, mul_sum, Complex.re_sum]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [mainCoeff, ← Complex.re_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [sum_congr rfl fun t _ => hper t, ← mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [← mul_sum, Complex.re_sum]

/-- **The prefix law of an oscillating log-polynomial.** For `0 < ε ≤ 1/2` and `n ≥ 1`,
`|A(n) − n^{1−ε} Σ_m (log n)^m Re(Σ_t q(t,m) n^{it})| ≤ C (√n)^{1−ε/2}`. -/
theorem abs_weightCenteredPrefix_oscillatingLogPolynomial_sub_le {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (J : Finset ℝ) (K : ℕ) (p : ℝ → ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix (oscillatingLogPolynomial ε J K p)
        (∑' d : ℕ, oscillatingLogPolynomial ε J K p d / d) n -
      (n : ℝ) ^ (1 - ε) * ∑ m ∈ range (K + 1), Real.log n ^ m *
        (∑ t ∈ J, mainCoeff ε K p t m * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re| ≤
      spectralRate ε J K p * Real.sqrt n ^ (1 - ε / 2) := by
  rw [weightCenteredPrefix_oscillatingLogPolynomial_eq hε]
  simp only [sum_logPower_floor_sub_eq hε hε2 hn, mul_add, add_re, sum_add_distrib]
  rw [sum_re_mul_leibniz_eq ε J K p hn, add_sub_cancel_right]
  calc |∑ t ∈ J, ∑ k ∈ range (K + 1),
          (p t k * iteratedDeriv k (floorRemainder n) (oscillationExponent ε t)).re|
      ≤ ∑ t ∈ J, ∑ k ∈ range (K + 1),
          ‖p t k‖ * (k.factorial * discRate ε t / (ε / 2) ^ k) * Real.sqrt n ^ (1 - ε / 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ =>
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_))
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul]
        have h := norm_iteratedDeriv_floorRemainder_le (t := t) hε hε2 hn k
        calc ‖p t k‖ * ‖iteratedDeriv k (floorRemainder n) (oscillationExponent ε t)‖
            ≤ ‖p t k‖ * (k.factorial * (discRate ε t * Real.sqrt n ^ (1 - ε / 2)) / (ε / 2) ^ k) :=
              mul_le_mul_of_nonneg_left h (norm_nonneg _)
          _ = _ := by ring
    _ = spectralRate ε J K p * Real.sqrt n ^ (1 - ε / 2) := by
        rw [spectralRate, sum_mul]
        exact sum_congr rfl fun t _ => by rw [sum_mul]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
