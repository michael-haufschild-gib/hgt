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
(`receiverBounded_logPowerCosine_iff`): the receiver reads the complete zero divisor of `ζ` in
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

/-! ### Multi-frequency window energy -/

/-- The oscillation `Re(Σ_{t ∈ J} c_t n^{it})`. -/
def oscSum (J : Finset ℝ) (c : ℝ → ℂ) (n : ℕ) : ℝ :=
  (∑ t ∈ J, c t * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re

theorem abs_oscSum_le {J : Finset ℝ} (c : ℝ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    |oscSum J c n| ≤ ∑ t ∈ J, ‖c t‖ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (sum_le_sum fun t _ => ?_))
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  simp

/-- `x^{it} conj(x^{is}) = x^{i(t−s)}` for `x > 0`. -/
theorem ofReal_cpow_mul_conj {x : ℝ} (hx : 0 < x) (t s : ℝ) :
    ((x : ℝ) : ℂ) ^ ((t : ℂ) * I) * (starRingEnd ℂ) (((x : ℝ) : ℂ) ^ ((s : ℂ) * I)) =
      ((x : ℝ) : ℂ) ^ (((t - s : ℝ) : ℂ) * I) := by
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have harg : ((x : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  have hc : (starRingEnd ℂ) (((x : ℝ) : ℂ) ^ ((s : ℂ) * I)) =
      ((x : ℝ) : ℂ) ^ (((-s : ℝ) : ℂ) * I) := by
    have h := Complex.cpow_conj ((x : ℝ) : ℂ) ((s : ℂ) * I) harg
    rw [Complex.conj_ofReal] at h
    rw [← h]
    congr 1
    simp [Complex.conj_ofReal, Complex.conj_I]
  rw [hc, ← Complex.cpow_add _ _ hx0]
  congr 1
  push_cast
  ring

/-- `Re(Σ_t c_t x^{it})² = ½ Σ_{t,s} [Re(c_t c̄_s x^{i(t−s)}) + Re(c_t c_s x^{i(t+s)})]`. -/
theorem oscSum_sq_eq {J : Finset ℝ} (c : ℝ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    oscSum J c n ^ 2 =
      (∑ t ∈ J, ∑ s ∈ J,
        ((c t * (starRingEnd ℂ) (c s) * ((n : ℝ) : ℂ) ^ (((t - s : ℝ) : ℂ) * I)).re +
          (c t * c s * ((n : ℝ) : ℂ) ^ (((t + s : ℝ) : ℂ) * I)).re)) / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  set z := ∑ t ∈ J, c t * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) with hz
  have hnorm : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have h1 : z * (starRingEnd ℂ) z = ∑ t ∈ J, ∑ s ∈ J,
      c t * (starRingEnd ℂ) (c s) * ((n : ℝ) : ℂ) ^ (((t - s : ℝ) : ℂ) * I) := by
    rw [hz, map_sum, sum_mul_sum]
    refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
    rw [map_mul, ← ofReal_cpow_mul_conj hn0 t s]
    ring
  have h2 : z ^ 2 = ∑ t ∈ J, ∑ s ∈ J, c t * c s * ((n : ℝ) : ℂ) ^ (((t + s : ℝ) : ℂ) * I) := by
    rw [hz, sq, sum_mul_sum]
    refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
    rw [show ((t + s : ℝ) : ℂ) * I = (t : ℂ) * I + (s : ℂ) * I by push_cast; ring,
      Complex.cpow_add _ _ hx0]
    ring
  rw [oscSum, ← hz, re_sq_eq_half, hnorm, h1, h2]
  simp only [Complex.re_sum, ← sum_add_distrib]

theorem oscHarmonicBound_nonneg (τ : ℝ) : 0 ≤ oscHarmonicBound τ := by
  unfold oscHarmonicBound
  exact add_nonneg (by positivity) (partialSumRate_nonneg (by simp))

theorem norm_sum_Ioc_cpow_div_le {τ : ℝ} (hτ : τ ≠ 0) {N T : ℕ} (hNT : N ≤ T) :
    ‖∑ n ∈ Ioc N T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((n : ℝ) : ℂ)‖ ≤ 2 * oscHarmonicBound τ := by
  rw [sum_Ioc_eq_sub _ hNT]
  have h1 := norm_sum_Icc_cpow_div_le hτ T
  have h2 := norm_sum_Icc_cpow_div_le hτ N
  exact (norm_sub_le _ _).trans (by linarith)

/-- The defect of a multi-frequency window: the cross frequencies `t ± s`. -/
def windowDefect (J : Finset ℝ) (c : ℝ → ℂ) : ℝ :=
  ∑ t ∈ J, ∑ s ∈ J, ‖c t‖ * ‖c s‖ * (oscHarmonicBound (t - s) + oscHarmonicBound (t + s))

/-- **Multi-frequency window energy.** For positive frequencies and `N ≤ T`,
`Σ_{N<n≤T} Re(Σ_t c_t n^{it})²/n ≥ (Σ_t |c_t|²/2) Σ_{N<n≤T} 1/n − D(J, c)`: distinct frequencies are
orthogonal up to the bounded harmonic sums at `t − s ≠ 0` and `t + s > 0`. -/
theorem sum_Ioc_oscSum_sq_div_ge {J : Finset ℝ} (hJ : ∀ t ∈ J, 0 < t) (c : ℝ → ℂ) {N T : ℕ}
    (hNT : N ≤ T) :
    (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * ∑ n ∈ Ioc N T, 1 / (n : ℝ) - windowDefect J c ≤
      ∑ n ∈ Ioc N T, oscSum J c n ^ 2 / n := by
  set S : ℝ → ℂ := fun τ => ∑ n ∈ Ioc N T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) / ((n : ℝ) : ℂ)
    with hS
  set H := ∑ n ∈ Ioc N T, 1 / (n : ℝ) with hH
  have hterm : ∀ n ∈ Ioc N T, oscSum J c n ^ 2 / n =
      (∑ t ∈ J, ∑ s ∈ J, ((c t * (starRingEnd ℂ) (c s) *
          (((n : ℝ) : ℂ) ^ (((t - s : ℝ) : ℂ) * I) / ((n : ℝ) : ℂ))).re +
        (c t * c s * (((n : ℝ) : ℂ) ^ (((t + s : ℝ) : ℂ) * I) / ((n : ℝ) : ℂ))).re)) / 2 := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
    rw [oscSum_sq_eq c hn1]
    simp only [← mul_div_assoc, Complex.div_ofReal_re, ← add_div, ← sum_div]
    ring
  have hexp : ∑ n ∈ Ioc N T, oscSum J c n ^ 2 / n =
      (∑ t ∈ J, ∑ s ∈ J, ((c t * (starRingEnd ℂ) (c s) * S (t - s)).re +
        (c t * c s * S (t + s)).re)) / 2 := by
    rw [sum_congr rfl hterm, ← sum_div, sum_comm]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum, ← mul_sum, ← mul_sum]
  have hpair : ∀ t ∈ J, ∀ s ∈ J,
      (if t = s then ‖c t‖ ^ 2 * H else 0) -
          2 * (‖c t‖ * ‖c s‖ * (oscHarmonicBound (t - s) + oscHarmonicBound (t + s))) ≤
        (c t * (starRingEnd ℂ) (c s) * S (t - s)).re + (c t * c s * S (t + s)).re := by
    intro t ht s hs
    have hts : t + s ≠ 0 := by have := hJ t ht; have := hJ s hs; linarith
    have hB1 := oscHarmonicBound_nonneg (t - s)
    have hS2 : ‖S (t + s)‖ ≤ 2 * oscHarmonicBound (t + s) := norm_sum_Ioc_cpow_div_le hts hNT
    have h2 : -(‖c t‖ * ‖c s‖ * (2 * oscHarmonicBound (t + s))) ≤ (c t * c s * S (t + s)).re := by
      refine neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans ?_)
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left hS2 (by positivity)
    split_ifs with hst
    · rw [← hst] at h2 hB1 ⊢
      have hS0 : S (t - t) = (H : ℂ) := by simp [hS, hH]
      have hcc : c t * (starRingEnd ℂ) (c t) = ((‖c t‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hS0, hcc, ← Complex.ofReal_mul, Complex.ofReal_re]
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (c t)) (norm_nonneg (c t))) hB1]
    · have hne : t - s ≠ 0 := sub_ne_zero.mpr hst
      have hS1 : ‖S (t - s)‖ ≤ 2 * oscHarmonicBound (t - s) := norm_sum_Ioc_cpow_div_le hne hNT
      have h1 : -(‖c t‖ * ‖c s‖ * (2 * oscHarmonicBound (t - s))) ≤
          (c t * (starRingEnd ℂ) (c s) * S (t - s)).re := by
        refine neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left hS1 (by positivity)
      linarith
  have hdiag : ∑ t ∈ J, ∑ s ∈ J, (if t = s then ‖c t‖ ^ 2 * H else 0) =
      (∑ t ∈ J, ‖c t‖ ^ 2) * H := by
    rw [sum_mul]
    exact sum_congr rfl fun t ht => by rw [sum_ite_eq, if_pos ht]
  have hdef : ∑ t ∈ J, ∑ s ∈ J,
      2 * (‖c t‖ * ‖c s‖ * (oscHarmonicBound (t - s) + oscHarmonicBound (t + s))) =
        2 * windowDefect J c := by
    rw [windowDefect, mul_sum]
    exact sum_congr rfl fun t _ => by rw [mul_sum]
  have hlow : (∑ t ∈ J, ‖c t‖ ^ 2) * H - 2 * windowDefect J c ≤
      ∑ t ∈ J, ∑ s ∈ J, ((c t * (starRingEnd ℂ) (c s) * S (t - s)).re +
        (c t * c s * S (t + s)).re) := by
    rw [← hdiag, ← hdef, ← sum_sub_distrib]
    exact sum_le_sum fun t ht => by
      rw [← sum_sub_distrib]; exact sum_le_sum fun s hs => hpair t ht s hs
  rw [hexp]
  linarith

/-! ### Descent in the log-degree -/

/-- **Power-amplified windows.** If `|w(n)| ≤ β (log n)^{K−1}` for `n ≥ 3`, `K ≥ 1`, and the window
energies of `v` satisfy `Σ_{N<n≤N²} v(n)²/n ≥ κ(log N − 1) − κ'` with `κ > 0`, then
`Σ_{n ≤ T} ((log n)^K v(n) + w(n))²/n` is unbounded. -/
theorem exists_lt_sum_sq_div_of_window_pow {v w : ℕ → ℝ} {β κ κ' : ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hκ : 0 < κ) (hw : ∀ n, 3 ≤ n → |w n| ≤ β * Real.log n ^ (K - 1))
    (hv : ∀ N : ℕ, 1 ≤ N → κ * (Real.log N - 1) - κ' ≤ ∑ n ∈ Ioc N (N ^ 2), v n ^ 2 / n)
    (C : ℝ) : ∃ T : ℕ, C < ∑ n ∈ Icc 1 T, (Real.log n ^ K * v n + w n) ^ 2 / n := by
  have hβ : 0 ≤ β := by
    have h := (abs_nonneg _).trans (hw 3 le_rfl)
    have hl : 0 < Real.log ((3 : ℕ) : ℝ) ^ (K - 1) :=
      pow_pos (Real.log_pos (by norm_num)) _
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hl
    linarith
  set γ := β ^ 2 * ((2 : ℝ) ^ (K - 1)) ^ 2 with hγ
  have hγ0 : 0 ≤ γ := by positivity
  set D := |C| + 3 * γ + 1 with hD
  have hD0 : 0 < D := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max 3 (Real.exp (1 + (|κ'| + 2 * D) / κ)))
  have hN3 : (3 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN3' : 3 ≤ N := by exact_mod_cast hN3.le
  have hN1 : 1 ≤ N := by omega
  set X := Real.log N with hXdef
  have hX : 1 + (|κ'| + 2 * D) / κ < X := by
    rw [hXdef, Real.lt_log_iff_exp_lt hN0]; exact lt_of_le_of_lt (le_max_right _ _) hN
  have hX1 : 1 ≤ X := by
    have : 0 ≤ (|κ'| + 2 * D) / κ := by positivity
    linarith
  have hX0 : 0 ≤ X := by linarith
  set P := (X ^ (K - 1)) ^ 2 with hP
  have hP1 : 1 ≤ P := one_le_pow₀ (one_le_pow₀ hX1)
  have hwin : P * (X ^ 2 / 2 * (κ * (X - 1) - κ') - γ * (1 + 2 * X)) ≤
      ∑ n ∈ Ioc N (N ^ 2), (Real.log n ^ K * v n + w n) ^ 2 / n := by
    have hterm : ∀ n ∈ Ioc N (N ^ 2), P * (X ^ 2 / 2 * (v n ^ 2 / n) - γ * (1 / (n : ℝ))) ≤
        (Real.log n ^ K * v n + w n) ^ 2 / n := by
      intro n hn
      have hNn := mem_Ioc.mp hn
      have hn3 : 3 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hL : X ≤ Real.log n := Real.log_le_log hN0 (by exact_mod_cast hNn.1.le)
      have hL2 : Real.log n ≤ 2 * X := by
        have h : Real.log n ≤ Real.log ((N : ℝ) ^ 2) :=
          Real.log_le_log hn0 (by exact_mod_cast hNn.2)
        rw [Real.log_pow, ← hXdef] at h
        push_cast at h
        exact h
      have hw2 : w n ^ 2 ≤ γ * P := by
        have h1 : |w n| ≤ β * (2 * X) ^ (K - 1) :=
          (hw n hn3).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) hL2 _) hβ)
        have h2 : w n ^ 2 ≤ (β * (2 * X) ^ (K - 1)) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        calc w n ^ 2 ≤ (β * (2 * X) ^ (K - 1)) ^ 2 := h2
          _ = γ * P := by rw [hγ, hP, mul_pow, mul_pow]; ring
      have hLv : P * X ^ 2 * v n ^ 2 ≤ (Real.log n ^ K * v n) ^ 2 := by
        have hXK : X ^ K ≤ Real.log n ^ K := pow_le_pow_left₀ hX0 hL K
        have e : (X ^ K) ^ 2 = P * X ^ 2 := by
          rw [hP, ← mul_pow, ← pow_succ, Nat.sub_add_cancel hK]
        rw [mul_pow, ← e]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg hX0 K) hXK 2)
          (sq_nonneg _)
      have hkey : P * (X ^ 2 / 2 * v n ^ 2 - γ) ≤ (Real.log n ^ K * v n + w n) ^ 2 := by
        nlinarith [sq_nonneg (Real.log n ^ K * v n + 2 * w n)]
      have e : P * (X ^ 2 / 2 * (v n ^ 2 / n) - γ * (1 / (n : ℝ))) =
          P * (X ^ 2 / 2 * v n ^ 2 - γ) / n := by ring
      rw [e]
      exact div_le_div_of_nonneg_right hkey hn0.le
    have h1 := hv N hN1
    have h2 := sum_Ioc_one_div_le hN1
    rw [← hXdef] at h1 h2
    have hX2 : 0 ≤ X ^ 2 / 2 := by positivity
    have hP0 : 0 ≤ P := by positivity
    calc P * (X ^ 2 / 2 * (κ * (X - 1) - κ') - γ * (1 + 2 * X))
        ≤ P * (X ^ 2 / 2 * ∑ n ∈ Ioc N (N ^ 2), v n ^ 2 / n -
            γ * ∑ n ∈ Ioc N (N ^ 2), 1 / (n : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hP0
          linarith [mul_le_mul_of_nonneg_left h1 hX2, mul_le_mul_of_nonneg_left h2 hγ0]
      _ = ∑ n ∈ Ioc N (N ^ 2), P * (X ^ 2 / 2 * (v n ^ 2 / n) - γ * (1 / (n : ℝ))) := by
          rw [← mul_sum, sum_sub_distrib, ← mul_sum, ← mul_sum]
      _ ≤ _ := sum_le_sum hterm
  have hsub : ∑ n ∈ Ioc N (N ^ 2), (Real.log n ^ K * v n + w n) ^ 2 / n ≤
      ∑ n ∈ Icc 1 (N ^ 2), (Real.log n ^ K * v n + w n) ^ 2 / n := by
    refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => by positivity)
    rw [mem_Ioc] at hn
    rw [mem_Icc]
    omega
  have hκX : 2 * D < κ * (X - 1) - κ' := by
    have h1 : (|κ'| + 2 * D) / κ < X - 1 := by linarith
    rw [div_lt_iff₀ hκ] at h1
    linarith [le_abs_self κ']
  have hbr : |C| + 1 ≤ X ^ 2 / 2 * (κ * (X - 1) - κ') - γ * (1 + 2 * X) := by
    have h1 := mul_le_mul_of_nonneg_left hκX.le (by positivity : (0 : ℝ) ≤ X ^ 2 / 2)
    have h2 := mul_le_mul_of_nonneg_right (show X ≤ X ^ 2 by nlinarith) hD0.le
    have h3 := mul_le_mul_of_nonneg_left (show 1 + 2 * X ≤ 3 * X by linarith) hγ0
    have h5 : |C| ≤ X * |C| := le_mul_of_one_le_left (abs_nonneg C) hX1
    have h6 : X * D = X * |C| + 3 * γ * X + X := by rw [hD]; ring
    linarith
  have hfin : |C| + 1 ≤ P * (X ^ 2 / 2 * (κ * (X - 1) - κ') - γ * (1 + 2 * X)) := by
    have hb0 : 0 ≤ X ^ 2 / 2 * (κ * (X - 1) - κ') - γ * (1 + 2 * X) := by
      linarith [abs_nonneg C]
    nlinarith [mul_nonneg (sub_nonneg.mpr hP1) hb0]
  exact ⟨N ^ 2, by linarith [le_abs_self C]⟩

/-- **The top log-coefficient of a paid main term vanishes.** If
`Σ_{n ≤ T} (Σ_{m ≤ K} (log n)^m Re(Σ_t q(t,m) n^{it}))²/n` is bounded, then `q(t, K) = 0` for every
positive frequency `t ∈ J`. -/
theorem top_coeff_eq_zero {J : Finset ℝ} (hJ : ∀ t ∈ J, 0 < t) (K : ℕ) (q : ℝ → ℕ → ℂ)
    {C : ℝ} (hC : ∀ T : ℕ, ∑ n ∈ Icc 1 T,
      (∑ m ∈ range (K + 1), Real.log n ^ m * oscSum J (q · m) n) ^ 2 / n ≤ C) :
    ∀ t ∈ J, q t K = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨t₀, ht₀, hq₀⟩ := hne
  have hκ0 : 0 < (∑ t ∈ J, ‖q t K‖ ^ 2) / 2 := by
    have : 0 < ∑ t ∈ J, ‖q t K‖ ^ 2 :=
      sum_pos' (fun t _ => sq_nonneg _) ⟨t₀, ht₀, by positivity⟩
    positivity
  have hwin : ∀ N : ℕ, 1 ≤ N → (∑ t ∈ J, ‖q t K‖ ^ 2) / 2 * (Real.log N - 1) -
      windowDefect J (q · K) ≤ ∑ n ∈ Ioc N (N ^ 2), oscSum J (q · K) n ^ 2 / n := by
    intro N hN
    have h1 := sum_Ioc_oscSum_sq_div_ge hJ (q · K) (le_self_pow hN two_ne_zero)
    beta_reduce at h1
    have h2 := mul_le_mul_of_nonneg_left (log_sub_one_le_sum_Ioc_one_div hN) hκ0.le
    linarith
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · -- degree zero: the window energy alone diverges
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (1 + (|windowDefect J (q · 0)| + |C| + 1) /
      ((∑ t ∈ J, ‖q t 0‖ ^ 2) / 2)))
    have hN0 : (0 : ℝ) < N := lt_trans (Real.exp_pos _) hN
    have hN1 : 1 ≤ N := Nat.cast_pos.mp hN0
    have hX := (Real.lt_log_iff_exp_lt hN0).mpr hN
    have h2 : (|windowDefect J (q · 0)| + |C| + 1) / ((∑ t ∈ J, ‖q t 0‖ ^ 2) / 2) <
        Real.log N - 1 := by linarith
    rw [div_lt_iff₀ hκ0] at h2
    have h1 := hwin N hN1
    have hsub : ∑ n ∈ Ioc N (N ^ 2), oscSum J (q · 0) n ^ 2 / n ≤
        ∑ n ∈ Icc 1 (N ^ 2), oscSum J (q · 0) n ^ 2 / n :=
      sum_le_sum_of_subset_of_nonneg
        (fun n hn => by rw [mem_Ioc] at hn; rw [mem_Icc]; omega) (fun n _ _ => by positivity)
    have h3 := hC (N ^ 2)
    simp only [zero_add, range_one, sum_singleton, pow_zero, one_mul] at h3
    linarith [le_abs_self C, le_abs_self (windowDefect J (q · 0))]
  · -- positive degree: the top power amplifies the window energy
    have hw : ∀ n : ℕ, 3 ≤ n → |∑ m ∈ range K, Real.log n ^ m * oscSum J (q · m) n| ≤
        (∑ m ∈ range K, ∑ t ∈ J, ‖q t m‖) * Real.log n ^ (K - 1) := by
      intro n hn
      have hn1 : 1 ≤ n := by omega
      have hL1 : 1 ≤ Real.log n := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have : (3 : ℝ) ≤ n := by exact_mod_cast hn
        linarith [Real.exp_one_lt_d9]
      calc |∑ m ∈ range K, Real.log n ^ m * oscSum J (q · m) n|
          ≤ ∑ m ∈ range K, |Real.log n ^ m * oscSum J (q · m) n| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ range K, Real.log n ^ (K - 1) * ∑ t ∈ J, ‖q t m‖ := sum_le_sum fun m hm => by
            rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith) m)]
            exact mul_le_mul (pow_le_pow_right₀ hL1 (by have := mem_range.mp hm; omega))
              (abs_oscSum_le (q · m) hn1) (abs_nonneg _) (pow_nonneg (by linarith) _)
        _ = (∑ m ∈ range K, ∑ t ∈ J, ‖q t m‖) * Real.log n ^ (K - 1) := by
            rw [← mul_sum, mul_comm]
    obtain ⟨T, hT⟩ := exists_lt_sum_sq_div_of_window_pow hK hκ0 hw hwin C
    have h := hC T
    have heq : ∀ n : ℕ, ∑ m ∈ range (K + 1), Real.log n ^ m * oscSum J (q · m) n =
        Real.log n ^ K * oscSum J (q · K) n +
          ∑ m ∈ range K, Real.log n ^ m * oscSum J (q · m) n :=
      fun n => by rw [Finset.sum_range_succ, add_comm]
    simp only [heq] at h
    linarith

/-- **A paid main term has no oscillating coefficients.** If
`Σ_{n ≤ T} (Σ_{m ≤ K} (log n)^m Re(Σ_t q(t,m) n^{it}))²/n` is bounded and all frequencies are
positive, then every `q(t, m)` vanishes. -/
theorem coeff_eq_zero_of_bounded {J : Finset ℝ} (hJ : ∀ t ∈ J, 0 < t) (K : ℕ) (q : ℝ → ℕ → ℂ)
    {C : ℝ} (hC : ∀ T : ℕ, ∑ n ∈ Icc 1 T,
      (∑ m ∈ range (K + 1), Real.log n ^ m * oscSum J (q · m) n) ^ 2 / n ≤ C) :
    ∀ t ∈ J, ∀ m ≤ K, q t m = 0 := by
  induction K with
  | zero =>
    intro t ht m hm
    rw [Nat.le_zero.mp hm]
    exact top_coeff_eq_zero hJ 0 q hC t ht
  | succ K ih =>
    have htop := top_coeff_eq_zero hJ (K + 1) q hC
    have hv0 : ∀ n : ℕ, oscSum J (q · (K + 1)) n = 0 := fun n => by
      simp only [oscSum]
      rw [sum_eq_zero fun t ht => by rw [htop t ht, zero_mul], zero_re]
    have hC' : ∀ T : ℕ, ∑ n ∈ Icc 1 T,
        (∑ m ∈ range (K + 1), Real.log n ^ m * oscSum J (q · m) n) ^ 2 / n ≤ C := by
      intro T
      have h := hC T
      simp only [Finset.sum_range_succ _ (K + 1), hv0, mul_zero, add_zero] at h
      exact h
    intro t ht m hm
    rcases Nat.lt_or_ge m (K + 1) with hlt | hge
    · exact ih hC' t ht m (by omega)
    · rw [show m = K + 1 by omega]
      exact htop t ht

/-! ### The spectral law -/

/-- **The receiver reads the zero divisor of ζ on the oscillating spectrum.** For `0 < ε ≤ 1/2`,
a finite set `J` of positive frequencies and coefficients `p(t, k)`, `k ≤ K`, the receiver of
`Σ_{t ∈ J} Σ_{k ≤ K} Re(p(t,k) d^{ρ_t − 1}(log d)^k)` is bounded iff for every `t ∈ J` and every
`k ≤ K` with `p(t, k) ≠ 0`, `ζ^{(i)}(1 − ε + it) = 0` for all `i ≤ k`. -/
theorem receiverBounded_oscillatingLogPolynomial_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {J : Finset ℝ} (hJ : ∀ t ∈ J, 0 < t) (K : ℕ) (p : ℝ → ℕ → ℂ) :
    ReceiverBounded (oscillatingLogPolynomial ε J K p) ↔
      ∀ t ∈ J, ∀ k ≤ K, p t k ≠ 0 → ∀ i ≤ k,
        iteratedDeriv i riemannZeta (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I) = 0 := by
  have hcoef : (∀ t ∈ J, ∀ m ≤ K, mainCoeff ε K p t m = 0) ↔
      ∀ t ∈ J, ∀ k ≤ K, p t k ≠ 0 → ∀ i ≤ k,
        iteratedDeriv i riemannZeta (oscillationExponent ε t) = 0 := by
    refine forall₂_congr fun t _ => ?_
    have hre : (oscillationExponent ε t).re = 1 - ε := oscillationExponent_re ε t
    have h0 : oscillationExponent ε t ≠ 0 := fun h => by rw [h, zero_re] at hre; linarith
    have h1 : oscillationExponent ε t ≠ 1 := fun h => by rw [h, one_re] at hre; linarith
    refine (forall_coeff_eq_zero_iff K (p t) (fun i =>
      iteratedDeriv i (fun s : ℂ => riemannZeta s / s) (oscillationExponent ε t))).trans ?_
    exact forall₂_congr fun k _ => imp_congr_right fun _ =>
      forall_iteratedDeriv_zeta_div_eq_zero_iff h0 h1 k
  refine Iff.trans ?_ hcoef
  constructor
  · intro hB
    obtain ⟨C, hC⟩ := exists_sum_sq_div_le_of_receiverBounded hB hε2
      (by linarith : (0 : ℝ) < ε / 2)
      (fun n hn => abs_weightCenteredPrefix_oscillatingLogPolynomial_sub_le hε hε2 J K p hn)
    exact coeff_eq_zero_of_bounded hJ K (mainCoeff ε K p) hC
  · intro h
    refine ⟨spectralRate ε J K p ^ 2 * (1 + 1 / (ε / 2)), fun T => ?_⟩
    rw [weightPronicEnergy]
    refine sum_sq_le_of_abs_le_sqrt_rpow (ε := ε / 2) (by linarith) (fun n hn => ?_) T
    have hb := abs_weightCenteredPrefix_oscillatingLogPolynomial_sub_le hε hε2 J K p hn
    have hz : ∑ m ∈ range (K + 1), Real.log n ^ m *
        (∑ t ∈ J, mainCoeff ε K p t m * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re = 0 :=
      sum_eq_zero fun m hm => by
        rw [sum_eq_zero fun t ht => by
          rw [h t ht m (by have := mem_range.mp hm; omega), zero_mul], zero_re, mul_zero]
    rwa [hz, mul_zero, sub_zero] at hb

/-- The log-power cosine `d^{-ε} cos(t log d) (log d)^k`. -/
def logPowerCosine (ε t : ℝ) (k d : ℕ) : ℝ := oscillatingSmoothPower ε t d * Real.log d ^ k

theorem logPowerCosine_eq {ε : ℝ} (hε : 0 < ε) (t : ℝ) (k : ℕ) :
    logPowerCosine ε t k =
      oscillatingLogPolynomial ε {t} k (fun _ j => if j = k then 1 else 0) := by
  funext d
  rw [oscillatingLogPolynomial, sum_singleton, sum_eq_single k
    (fun j _ hj => by rw [if_neg hj, zero_mul, zero_re])
    (fun h => absurd (mem_range.mpr (Nat.lt_succ_self k)) h), if_pos rfl, one_mul,
    logPowerOscillation, logPowerCosine, oscillatingSmoothPower_eq_re hε, ← Complex.ofReal_pow,
    Complex.re_mul_ofReal]

/-- **The receiver reads the order of every zero.** For `0 < ε ≤ 1/2`, `t > 0` and `k ∈ ℕ`, the
receiver of `d^{-ε} cos(t log d) (log d)^k` is bounded iff `ζ^{(i)}(1 − ε + it) = 0` for every
`i ≤ k`, that is, iff `1 − ε + it` is a zero of `ζ` of order greater than `k`. -/
theorem receiverBounded_logPowerCosine_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {t : ℝ}
    (ht : 0 < t) (k : ℕ) :
    ReceiverBounded (logPowerCosine ε t k) ↔
      ∀ i ≤ k, iteratedDeriv i riemannZeta (((1 - ε : ℝ) : ℂ) + (t : ℂ) * I) = 0 := by
  rw [logPowerCosine_eq hε,
    receiverBounded_oscillatingLogPolynomial_iff hε hε2 (by simpa using ht) k]
  constructor
  · intro h
    exact h t (mem_singleton_self t) k le_rfl (by simp)
  · intro h t' ht' j _ hp i hi
    rw [mem_singleton] at ht'
    subst ht'
    have hjk : j = k := by
      by_contra hne
      exact hp (if_neg hne)
    exact h i (hjk ▸ hi)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
