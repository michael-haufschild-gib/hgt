import GaloisForLFunctions.RHTower.XiReciprocalSliceNearestZero
import GaloisForLFunctions.RHTower.XiHorizontalSlicePolyaFrequencyCriterion
import GaloisForLFunctions.HTGeometry.ToeplitzHessenbergReciprocal

/-!
# Total positivity at one height puts the nearest zero on the critical line

The horizontal pair product `h_t(σ) = Ξ(t+σ)Ξ(t−σ)` is the slice `g_t` in the imaginary direction:
`h_t(σ) = g_t(iσ)`.  So `h_t(σ) = Σ_k (−1)^k a_k σ^{2k}` with `a_k = c_{2k}(t)` the slice
coefficients.  The Taylor coefficients `β_m` of `1/h_t` in `σ²` therefore solve
`Σ_{k ≤ m} (−1)^k a_k β_{m−k} = [m = 0]`.  By the Hessenberg–Wronski identity
(`HTGeometry.pow_mul_eq_toeplitzMinor_hessenberg`), `a₀^{m+1} β_m` is a Toeplitz minor of `(a_k)`.

* `xiReciprocalSlicePositive_of_forall_pfSeq`: if `Ξ(t) ≠ 0` and the slice coefficients at height
  `t` are `PF_k` for every `k`, then reciprocal slice positivity holds at `t`.
* `xiReciprocalSlicePositive_of_riemannHypothesis`: RH gives reciprocal slice positivity at
  every height with `Ξ(t) ≠ 0`.
* **Single-height converse** (`xi_critical_zero_at_nearest_distance_of_forall_pfSeq`): if the
  slice at height `t` is totally positive (`PF_k` for all `k`), then the distance from `½ + it` to
  the zeros of `ξ` is attained at a critical zero.  Each finite order `k` is implied by a
  zero-free cone of half-angle `π/(2k+2)` (`XiHorizontalSlicePolyaFrequencyCone`).  Conversely,
  infinite order at a single height locates the nearest zero on the critical line.
-/

open Complex Filter Topology
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The pair product is the slice in the imaginary direction. -/
theorem xiHorizontalPair_eq_xiSliceProduct (t : ℝ) (σ : ℂ) :
    xiHorizontalPair t σ = xiSliceProduct t (I * σ) := by
  unfold xiHorizontalPair XiC xiSliceProduct
  congr 2 <;> ring

theorem xiHorizontalPair_neg (t : ℝ) (σ : ℂ) : xiHorizontalPair t (-σ) = xiHorizontalPair t σ := by
  unfold xiHorizontalPair
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

theorem xiHorizontalPair_conj (t : ℝ) (σ : ℂ) :
    xiHorizontalPair t ((starRingEnd ℂ) σ) = (starRingEnd ℂ) (xiHorizontalPair t σ) := by
  unfold xiHorizontalPair
  rw [map_mul, ← XiC_conj, ← XiC_conj, map_add, map_sub, Complex.conj_ofReal]

/-- Taylor coefficients of the pair product: `(n!)⁻¹ h_t^{(n)}(0) = iⁿ c_n(t)`. -/
theorem factorial_inv_mul_iteratedDeriv_xiHorizontalPair (t : ℝ) (n : ℕ) :
    ((n.factorial : ℂ))⁻¹ * iteratedDeriv n (xiHorizontalPair t) 0 = I ^ n * xiSliceCoeff t n := by
  have hfun : xiHorizontalPair t = fun σ => xiSliceProduct t (I * σ) :=
    funext (xiHorizontalPair_eq_xiSliceProduct t)
  rw [hfun, iteratedDeriv_comp_const_mul (differentiable_xiSliceProduct t).contDiff I]
  simp only [mul_zero]
  unfold xiSliceCoeff
  ring

/-- The reciprocal pair product has vanishing odd Taylor coefficients at `0`. -/
theorem iteratedDeriv_inv_xiHorizontalPair_odd (t : ℝ) (m : ℕ) :
    iteratedDeriv (2 * m + 1) (fun σ => (xiHorizontalPair t σ)⁻¹) 0 = 0 := by
  have h := iteratedDeriv_comp_neg (2 * m + 1) (fun σ => (xiHorizontalPair t σ)⁻¹) 0
  have e : (fun σ => (xiHorizontalPair t (-σ))⁻¹) = fun σ => (xiHorizontalPair t σ)⁻¹ :=
    funext fun σ => by rw [xiHorizontalPair_neg]
  rw [e, neg_zero, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_smul] at h
  linear_combination (1 / 2 : ℂ) * h

/-- The reciprocal pair product has real Taylor coefficients at `0`. -/
theorem im_iteratedDeriv_inv_xiHorizontalPair (t : ℝ) (n : ℕ) :
    (iteratedDeriv n (fun σ => (xiHorizontalPair t σ)⁻¹) 0).im = 0 := by
  have hsym : (starRingEnd ℂ) ∘ (fun σ => (xiHorizontalPair t σ)⁻¹) ∘ (starRingEnd ℂ) =
      fun σ => (xiHorizontalPair t σ)⁻¹ := by
    funext σ
    simp only [Function.comp_apply, xiHorizontalPair_conj, map_inv₀, Complex.conj_conj]
  have h := congrFun (iteratedDeriv_conj_comp_conj (fun σ => (xiHorizontalPair t σ)⁻¹) n) 0
  rw [hsym] at h
  simp only [Function.comp_apply, map_zero] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- The normalized Leibniz identity for `h_t · (1/h_t) = 1` at even order. -/
theorem sum_xiHorizontalPair_mul_inv_even {t : ℝ} (h0 : XiC t ≠ 0) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
        ((((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) (xiHorizontalPair t) 0) *
          ((((2 * (m - j)).factorial : ℂ))⁻¹ *
            iteratedDeriv (2 * (m - j)) (fun σ => (xiHorizontalPair t σ)⁻¹) 0) =
      if m = 0 then 1 else 0 := by
  set f := xiHorizontalPair t with hf
  set g : ℂ → ℂ := fun σ => (f σ)⁻¹ with hg
  have hf0 : f 0 ≠ 0 := by
    rw [hf]
    unfold xiHorizontalPair
    simpa using mul_ne_zero h0 h0
  have hfa : AnalyticAt ℂ f 0 := (differentiable_xiHorizontalPair t).analyticAt 0
  have hga : AnalyticAt ℂ g 0 := hfa.inv hf0
  have hfg : (f * g) =ᶠ[𝓝 0] fun _ => (1 : ℂ) := by
    filter_upwards [(differentiable_xiHorizontalPair t).continuous.continuousAt.eventually_ne hf0]
      with σ hσ
    simp only [Pi.mul_apply, hg]
    exact mul_inv_cancel₀ hσ
  have hfo : ∀ k : ℕ, iteratedDeriv (2 * k + 1) f 0 = 0 := by
    intro k
    have h := factorial_inv_mul_iteratedDeriv_xiHorizontalPair t (2 * k + 1)
    rw [xiSliceCoeff_odd_eq_zero, mul_zero] at h
    have hfac : (((2 * k + 1).factorial : ℂ))⁻¹ ≠ 0 :=
      inv_ne_zero (by exact_mod_cast (Nat.factorial_pos _).ne')
    exact (mul_eq_zero.mp h).resolve_left hfac
  have hL := (hfg.iteratedDeriv_eq (2 * m)).symm
  rw [iteratedDeriv_const] at hL
  rw [iteratedDeriv_mul hfa.contDiffAt hga.contDiffAt] at hL
  have hterm : ∀ i ∈ Finset.range (2 * m + 1),
      (((2 * m).factorial : ℂ))⁻¹ *
          (((2 * m).choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (2 * m - i) g 0) =
        (((i.factorial : ℂ))⁻¹ * iteratedDeriv i f 0) *
          ((((2 * m - i).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m - i) g 0) := by
    intro i hi
    have hik : i ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hfac : ((2 * m).choose i : ℂ) * (i.factorial : ℂ) * ((2 * m - i).factorial : ℂ) =
        ((2 * m).factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
    have h1 : ((2 * m).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h2 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h3 : ((2 * m - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    field_simp
    linear_combination (iteratedDeriv i f 0 * iteratedDeriv (2 * m - i) g 0) * hfac
  have hsum : (((2 * m).factorial : ℂ))⁻¹ * (if 2 * m = 0 then (1 : ℂ) else 0) =
      ∑ j ∈ Finset.range (m + 1),
        ((((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) f 0) *
          ((((2 * (m - j)).factorial : ℂ))⁻¹ * iteratedDeriv (2 * (m - j)) g 0) := by
    rw [hL, Finset.mul_sum, Finset.sum_congr rfl hterm]
    refine sum_range_two_mul_add_one_eq_even _ (fun j => by rw [hfo j]; simp) m |>.trans ?_
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show 2 * m - 2 * j = 2 * (m - j) by omega]
  rw [← hsum]
  by_cases hm : m = 0
  · subst hm
    simp
  · have h2m : 2 * m ≠ 0 := by omega
    rw [if_neg h2m, if_neg hm, mul_zero]

/-- The even reciprocal relation at height `t`:
`Σ_{k ≤ m} (−1)^k c_{2k}(t) β_{m−k}(t) = [m = 0]`, with `β_m(t)` the coefficient of `σ^{2m}` in
`1/h_t(σ)`. -/
theorem sum_xiSliceCoeff_mul_inv_even {t : ℝ} (h0 : XiC t ≠ 0) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ k * (xiSliceCoeff t (2 * k)).re *
      ((((2 * (m - k)).factorial : ℂ))⁻¹ *
        iteratedDeriv (2 * (m - k)) (fun σ => (xiHorizontalPair t σ)⁻¹) 0).re =
      if m = 0 then 1 else 0 := by
  set a : ℕ → ℝ := fun n => (xiSliceCoeff t (2 * n)).re with ha
  set g : ℂ → ℂ := fun σ => (xiHorizontalPair t σ)⁻¹ with hg
  set β : ℕ → ℝ := fun m => ((((2 * m).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m) g 0).re
    with hβdef
  have hβreal : ∀ m, ((((2 * m).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m) g 0) = (β m : ℂ) := by
    intro m
    apply Complex.ext
    · simp [hβdef]
    · rw [Complex.mul_im, im_iteratedDeriv_inv_xiHorizontalPair, mul_zero, zero_add,
        Complex.ofReal_im]
      have : ((((2 * m).factorial : ℂ))⁻¹).im = 0 := by
        rw [show (((2 * m).factorial : ℂ))⁻¹ = ((((2 * m).factorial : ℝ))⁻¹ : ℝ) by
          push_cast; rfl]
        exact Complex.ofReal_im _
      rw [this, zero_mul]
  have hfcoef : ∀ j, ((((2 * j).factorial : ℂ))⁻¹ * iteratedDeriv (2 * j) (xiHorizontalPair t) 0)
      = (((-1 : ℝ) ^ j * a j : ℝ) : ℂ) := by
    intro j
    rw [factorial_inv_mul_iteratedDeriv_xiHorizontalPair, pow_mul, Complex.I_sq]
    have hre : xiSliceCoeff t (2 * j) = (((xiSliceCoeff t (2 * j)).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [xiSliceCoeff_im_eq_zero]
    rw [hre]
    push_cast
    rfl
  have h := sum_xiHorizontalPair_mul_inv_even h0 m
  simp only [hfcoef, ← hg, hβreal] at h
  have h' := congrArg Complex.re h
  rw [Complex.re_sum] at h'
  simp only [← Complex.ofReal_mul, Complex.ofReal_re] at h'
  show ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ k * a k * β (m - k) = _
  rw [h']
  split_ifs <;> simp

/-- The first slice coefficient `c₀(t) = Ξ(t)²` is positive off the zeros. -/
theorem xiSliceCoeff_zero_re_pos {t : ℝ} (h0 : XiC t ≠ 0) : 0 < (xiSliceCoeff t (2 * 0)).re := by
  have hc0 : xiSliceCoeff t 0 = XiC t * XiC t := by
    simp only [xiSliceCoeff, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
      iteratedDeriv_zero]
    unfold xiSliceProduct XiC
    simp only [add_zero, sub_zero]
  have hreal : (XiC t).im = 0 := by
    have h := XiC_conj (t : ℂ)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hre0 : (XiC t).re ≠ 0 := by
    intro hre
    exact h0 (Complex.ext hre hreal)
  rw [mul_zero, hc0, Complex.mul_re, hreal, mul_zero, sub_zero]
  exact mul_self_pos.mpr hre0

/-- **Total positivity at one height gives reciprocal slice positivity.** -/
theorem xiReciprocalSlicePositive_of_forall_pfSeq {t : ℝ} (h0 : XiC t ≠ 0)
    (hpf : ∀ k, PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)) :
    XiReciprocalSlicePositive t := by
  set a : ℕ → ℝ := fun n => (xiSliceCoeff t (2 * n)).re with ha
  set g : ℂ → ℂ := fun σ => (xiHorizontalPair t σ)⁻¹ with hg
  set β : ℕ → ℝ := fun m => ((((2 * m).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m) g 0).re
    with hβdef
  have hβreal : ∀ m, ((((2 * m).factorial : ℂ))⁻¹ * iteratedDeriv (2 * m) g 0) = (β m : ℂ) := by
    intro m
    apply Complex.ext
    · simp [hβdef]
    · rw [Complex.mul_im, im_iteratedDeriv_inv_xiHorizontalPair, mul_zero, zero_add,
        Complex.ofReal_im]
      have : ((((2 * m).factorial : ℂ))⁻¹).im = 0 := by
        rw [show (((2 * m).factorial : ℂ))⁻¹ = ((((2 * m).factorial : ℝ))⁻¹ : ℝ) by
          push_cast; rfl]
        exact Complex.ofReal_im _
      rw [this, zero_mul]
  have hrec : ∀ m, ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ k * a k * β (m - k) =
      if m = 0 then 1 else 0 := sum_xiSliceCoeff_mul_inv_even h0
  have ha0 : 0 < a 0 := xiSliceCoeff_zero_re_pos h0
  intro n
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hβm : 0 ≤ β m := hessenberg_reciprocal_nonneg (hpf m) ha0 hrec le_rfl
    have hfac : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hD : iteratedDeriv (2 * m) g 0 = ((((2 * m).factorial : ℝ) * β m : ℝ) : ℂ) := by
      have h := hβreal m
      have hne : (((2 * m).factorial : ℂ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      push_cast
      rw [← h]
      field_simp
    show 0 ≤ iteratedDeriv (2 * m) g 0
    rw [hD]
    exact Complex.zero_le_real.mpr (mul_nonneg hfac.le hβm)
  · show 0 ≤ iteratedDeriv (2 * m + 1) g 0
    rw [iteratedDeriv_inv_xiHorizontalPair_odd]

/-- **RH gives reciprocal slice positivity at every height off the critical zeros.** -/
theorem xiReciprocalSlicePositive_of_riemannHypothesis (hRH : RiemannHypothesis) {t : ℝ}
    (h0 : XiC t ≠ 0) : XiReciprocalSlicePositive t :=
  xiReciprocalSlicePositive_of_forall_pfSeq h0
    (riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff.mp hRH t)

/-- **Single-height converse of the visibility-cone law.**  If the slice coefficients at height
`t` are `PF_k` for every `k`, then for every zero `ρ` of `ξ` nearest to `½ + it`, `ξ` vanishes at
`½ + i(t + d)` or at `½ + i(t − d)`, where `d = ‖ρ − (½ + it)‖`. -/
theorem xi_critical_zero_at_nearest_distance_of_forall_pfSeq {t : ℝ}
    (hpf : ∀ k, PFSeq k (fun n => (xiSliceCoeff t (2 * n)).re)) {ρ : ℂ} (hρ : xi ρ = 0)
    (hmin : ∀ ρ' : ℂ, xi ρ' = 0 → ‖ρ - (1 / 2 + t * I)‖ ≤ ‖ρ' - (1 / 2 + t * I)‖) :
    xi (1 / 2 + ((t + ‖ρ - (1 / 2 + t * I)‖ : ℝ) : ℂ) * I) = 0 ∨
      xi (1 / 2 + ((t - ‖ρ - (1 / 2 + t * I)‖ : ℝ) : ℂ) * I) = 0 := by
  by_cases h0 : XiC t = 0
  · have hzero : xi (1 / 2 + (t : ℂ) * I) = 0 := h0
    have hd : ‖ρ - (1 / 2 + t * I)‖ = 0 := by
      have := hmin _ hzero
      rw [sub_self, norm_zero] at this
      exact le_antisymm this (norm_nonneg _)
    left
    rw [hd, add_zero]
    exact hzero
  · exact xi_critical_zero_at_nearest_distance_of_reciprocal_nonneg
      (xiReciprocalSlicePositive_of_forall_pfSeq h0 hpf) hρ hmin

end

end RHTower
