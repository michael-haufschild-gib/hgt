import GaloisForLFunctions.HTGeometry.CircleFejerKernel

/-!
# Fejer polynomials for the F. and M. Riesz argument

Given two integrable complex densities whose nonnegative analytic moments agree, this module
constructs the finite analytic Fejer polynomial of the remaining moment half-line.  Its boundary
values are an exact Fejer convolution, and its normalized boundary `L¹` norm is uniformly bounded
by the two density norms.
-/

open MeasureTheory Complex Filter Topology Set Polynomial PowerSeries Finset
open scoped Real ENNReal NNReal Nat ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complex form of the real, nonnegative circle Fejer kernel. -/
noncomputable def circleFejerKernelC (N : ℕ) (theta : ℝ) (w : Circle) : ℂ :=
  ((N + 1 : ℂ)⁻¹) *
    (∑ j ∈ Finset.range (N + 1),
      (((starRingEnd ℂ) (w : ℂ)) ^ j) * (circleMap 0 1 theta) ^ j) *
    (starRingEnd ℂ) (∑ j ∈ Finset.range (N + 1),
      (((starRingEnd ℂ) (w : ℂ)) ^ j) * (circleMap 0 1 theta) ^ j)

theorem circleFejerKernelC_eq_coe (N : ℕ) (theta : ℝ) (w : Circle) :
    circleFejerKernelC N theta w = (circleFejerKernel N theta w : ℂ) := by
  unfold circleFejerKernelC circleFejerKernel
  let S : ℂ := ∑ j ∈ Finset.range (N + 1),
    ((starRingEnd ℂ) (w : ℂ)) ^ j * circleMap 0 1 theta ^ j
  change ((N + 1 : ℂ)⁻¹) * S * (starRingEnd ℂ) S =
    (((N + 1 : ℝ)⁻¹ * ‖S‖ ^ 2 : ℝ) : ℂ)
  calc
    ((N + 1 : ℂ)⁻¹) * S * (starRingEnd ℂ) S =
        ((N + 1 : ℂ)⁻¹) * (S * (starRingEnd ℂ) S) := by ring
    _ = ((N + 1 : ℂ)⁻¹) * (‖S‖ ^ 2 : ℝ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = (((N + 1 : ℝ)⁻¹ * ‖S‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring

theorem circleFejerKernelC_eq_doubleSum (N : ℕ) (theta : ℝ) (w : Circle) :
    circleFejerKernelC N theta w =
      ((N + 1 : ℂ)⁻¹) * ∑ j ∈ Finset.range (N + 1),
        ∑ k ∈ Finset.range (N + 1),
          (((starRingEnd ℂ) (w : ℂ)) ^ j * circleMap 0 1 theta ^ j) *
            (starRingEnd ℂ)
              (((starRingEnd ℂ) (w : ℂ)) ^ k * circleMap 0 1 theta ^ k) := by
  unfold circleFejerKernelC
  rw [map_sum, mul_assoc, Finset.sum_mul]
  apply congrArg (((N + 1 : ℂ)⁻¹) * .)
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]

theorem pow_mul_conj_pow_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) (j k : ℕ) :
    u ^ j * (starRingEnd ℂ) (u ^ k) =
      if k ≤ j then u ^ (j - k) else (starRingEnd ℂ) (u ^ (k - j)) := by
  have hunit : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  split_ifs with hkj
  · calc
      u ^ j * (starRingEnd ℂ) (u ^ k) =
          (u ^ (j - k) * u ^ k) * (starRingEnd ℂ) (u ^ k) := by
            rw [← pow_add, Nat.sub_add_cancel hkj]
      _ = u ^ (j - k) * ((u * (starRingEnd ℂ) u) ^ k) := by
        rw [map_pow, mul_pow]
        ring
      _ = u ^ (j - k) := by rw [hunit, one_pow, mul_one]
  · have hjk : j ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge hkj)
    calc
      u ^ j * (starRingEnd ℂ) (u ^ k) =
          u ^ j * (starRingEnd ℂ) (u ^ j * u ^ (k - j)) := by
            rw [← pow_add]
            congr 3
            omega
      _ = ((u * (starRingEnd ℂ) u) ^ j) *
          (starRingEnd ℂ) (u ^ (k - j)) := by
        rw [map_mul, map_pow, mul_pow]
        ring
      _ = (starRingEnd ℂ) (u ^ (k - j)) := by rw [hunit, one_pow, one_mul]

/-- The unvanished positive moment of the two-density difference. -/
noncomputable def fAndMRemainingMoment
    (mu nu : Measure Circle) (f g : Circle → ℂ) (n : ℕ) : ℂ :=
  (∫ w, f w * (w : ℂ) ^ n ∂mu) - ∫ w, g w * (w : ℂ) ^ n ∂nu

/-- Finite analytic Fejer polynomial assembled from the remaining moment half-line. -/
noncomputable def fAndMFejerPolynomial
    (mu nu : Measure Circle) (f g : Circle → ℂ) (N : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
    if k < j then Polynomial.monomial (j - k)
      (((N + 1 : ℂ)⁻¹ * (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g (j - k))))
    else 0

theorem fAndMFejerPolynomial_eval
    (mu nu : Measure Circle) (f g : Circle → ℂ) (N : ℕ) (z : ℂ) :
    (fAndMFejerPolynomial mu nu f g N).eval z =
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        if k < j then ((N + 1 : ℂ)⁻¹ *
          (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g (j - k))) * z ^ (j - k)
        else 0 := by
  rw [fAndMFejerPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp_all

/-- Each positive coefficient is the corresponding remaining moment times the Fejer weight. -/
theorem fAndMFejerPolynomial_coeff_of_pos_of_le
    (mu nu : Measure Circle) (f g : Circle → ℂ) (N n : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) :
    (fAndMFejerPolynomial mu nu f g N).coeff n =
      ((N + 1 - n : ℂ) * (N + 1 : ℂ)⁻¹) *
        (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n) := by
  rw [fAndMFejerPolynomial, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.finsetSum_coeff]
  let c : ℕ → ℂ := fun d => (N + 1 : ℂ)⁻¹ *
    (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g d)
  have hrewrite :
      (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        (if k < j then Polynomial.monomial (j - k) (c (j - k)) else 0).coeff n) =
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        if k < j ∧ j - k = n then c n else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkj : k < j
    · rw [if_pos hkj, Polynomial.coeff_monomial]
      by_cases heq : j - k = n
      · simp [hkj, heq]
      · simp [hkj, heq]
    · simp [hkj]
  change (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
    (if k < j then Polynomial.monomial (j - k) (c (j - k)) else 0).coeff n) = _
  rw [hrewrite]
  have hinner : ∀ j ∈ Finset.range (N + 1),
      (∑ k ∈ Finset.range (N + 1), if k < j ∧ j - k = n then c n else 0) =
        if n ≤ j then c n else 0 := by
    intro j hj
    by_cases hnj : n ≤ j
    · rw [if_pos hnj]
      have hmem : j - n ∈ Finset.range (N + 1) := by
        rw [Finset.mem_range] at hj ⊢
        omega
      rw [Finset.sum_eq_single_of_mem (j - n) hmem]
      · rw [if_pos]
        constructor <;> omega
      · intro k hk hne
        rw [if_neg]
        intro hcond
        apply hne
        omega
    · rw [if_neg hnj]
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg]
      intro hcond
      omega
  calc
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        if k < j ∧ j - k = n then c n else 0) =
        ∑ j ∈ Finset.range (N + 1), if n ≤ j then c n else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hinner j hj
    _ = ∑ j ∈ Finset.Ico n (N + 1), c n := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp [Finset.mem_Ico, and_comm]
    _ = (N + 1 - n : ℕ) • c n := by
      rw [Finset.sum_const, Nat.card_Ico]
    _ = ((N + 1 - n : ℂ) * (N + 1 : ℂ)⁻¹) *
        (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n) := by
      rw [nsmul_eq_mul]
      unfold c
      rw [Nat.cast_sub (by omega : n ≤ N + 1)]
      push_cast
      ring

/-- Every fixed positive coefficient of the finite Fejer polynomials converges to the
corresponding conjugated remaining moment. -/
theorem tendsto_fAndMFejerPolynomial_coeff_of_pos
    (mu nu : Measure Circle) (f g : Circle → ℂ) (n : ℕ) (hn : 0 < n) :
    Tendsto (fun N : ℕ => (fAndMFejerPolynomial mu nu f g N).coeff n) atTop
      (nhds ((starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n))) := by
  have hInv : Tendsto (fun N : ℕ => 1 / ((N : ℂ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hWeight :
      Tendsto (fun N : ℕ => (1 : ℂ) - (n : ℂ) * (1 / ((N : ℂ) + 1)))
        atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1)).sub
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (n : ℂ)) atTop (nhds (n : ℂ))).mul
          hInv))
  have hMoment : Tendsto
      (fun _ : ℕ => (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n)) atTop
      (nhds ((starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n))) := tendsto_const_nhds
  have hProduct := hWeight.mul hMoment
  simp only [one_mul] at hProduct
  refine Tendsto.congr' ?_ hProduct
  filter_upwards [eventually_ge_atTop n] with N hN
  rw [fAndMFejerPolynomial_coeff_of_pos_of_le mu nu f g N n hn hN]
  apply congrArg (fun z : ℂ => z * (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g n))
  have hden : (N : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero N
  field_simp

private theorem integral_conj_circle_pow_mul_conj_eq
    (mu : Measure Circle) (f : Circle → ℂ) (n : ℕ) :
    (∫ w, ((starRingEnd ℂ) (w : ℂ)) ^ n * (starRingEnd ℂ) (f w) ∂mu) =
      (starRingEnd ℂ) (∫ w, f w * (w : ℂ) ^ n ∂mu) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with w
  simp [map_mul, map_pow, mul_comm]

private theorem integral_circle_pow_mul_conj_eq
    (mu : Measure Circle) (f : Circle → ℂ) (n : ℕ) :
    (∫ w, (w : ℂ) ^ n * (starRingEnd ℂ) (f w) ∂mu) =
      (starRingEnd ℂ)
        (∫ w, f w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂mu) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with w
  simp [map_mul, map_pow, mul_comm]

private theorem integral_fejer_term_conj_sub
    (mu nu : Measure Circle) (f g : Circle → ℂ)
    (hvanish : ∀ n : ℕ,
      (∫ w, f w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂mu) =
        ∫ w, g w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂nu)
    (theta : ℝ) (j k : ℕ) :
    (∫ w, (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
        (starRingEnd ℂ)
          (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
        (starRingEnd ℂ) (f w) ∂mu) -
      (∫ w, (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
        (starRingEnd ℂ)
          (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
        (starRingEnd ℂ) (g w) ∂nu) =
      if k < j then circleMap 0 1 theta ^ (j - k) *
        (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g (j - k)) else 0 := by
  have hunit (w : Circle) :
      ‖circleMap 0 1 theta * (starRingEnd ℂ) (w : ℂ)‖ = 1 := by
    rw [norm_mul, norm_circleMap_zero]
    simp
  by_cases hkj : k < j
  · rw [if_pos hkj]
    have hle : k ≤ j := hkj.le
    have hmuPoint : (λ w : Circle =>
        (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
          (starRingEnd ℂ)
            (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
          (starRingEnd ℂ) (f w)) =
        fun w : Circle => circleMap 0 1 theta ^ (j - k) *
          (((starRingEnd ℂ) (w : ℂ)) ^ (j - k) * (starRingEnd ℂ) (f w)) := by
      funext w
      rw [pow_mul_conj_pow_of_norm_one (hunit w) j k, if_pos hle, mul_pow]
      ring
    have hnuPoint : (λ w : Circle =>
        (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
          (starRingEnd ℂ)
            (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
          (starRingEnd ℂ) (g w)) =
        fun w : Circle => circleMap 0 1 theta ^ (j - k) *
          (((starRingEnd ℂ) (w : ℂ)) ^ (j - k) * (starRingEnd ℂ) (g w)) := by
      funext w
      rw [pow_mul_conj_pow_of_norm_one (hunit w) j k, if_pos hle, mul_pow]
      ring
    rw [hmuPoint, hnuPoint, integral_const_mul, integral_const_mul,
      integral_conj_circle_pow_mul_conj_eq,
      integral_conj_circle_pow_mul_conj_eq, fAndMRemainingMoment, map_sub]
    ring
  · rw [if_neg hkj]
    have hjk : j ≤ k := Nat.le_of_not_gt hkj
    by_cases heq : j = k
    · subst k
      have hmuPoint : (λ w : Circle =>
          (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
            (starRingEnd ℂ)
              (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j)) *
            (starRingEnd ℂ) (f w)) = fun w : Circle => (starRingEnd ℂ) (f w) := by
        funext w
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hunit w, one_pow]
        norm_num
      have hnuPoint : (λ w : Circle =>
          (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
            (starRingEnd ℂ)
              (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j)) *
            (starRingEnd ℂ) (g w)) = fun w : Circle => (starRingEnd ℂ) (g w) := by
        funext w
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hunit w, one_pow]
        norm_num
      have hzero : (∫ w, f w ∂mu) = ∫ w, g w ∂nu := by
        simpa using hvanish 0
      rw [hmuPoint, hnuPoint, integral_conj, integral_conj, hzero, sub_self]
    · have hlt : j < k := lt_of_le_of_ne hjk heq
      have hnle : ¬k ≤ j := Nat.not_le.mpr hlt
      have hmuPoint : (λ w : Circle =>
          (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
            (starRingEnd ℂ)
              (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
            (starRingEnd ℂ) (f w)) =
          fun w : Circle => (starRingEnd ℂ) (circleMap 0 1 theta ^ (k - j)) *
            ((w : ℂ) ^ (k - j) * (starRingEnd ℂ) (f w)) := by
        funext w
        rw [pow_mul_conj_pow_of_norm_one (hunit w) j k, if_neg hnle]
        simp only [map_pow, map_mul, starRingEnd_self_apply]
        rw [mul_pow]
        ring
      have hnuPoint : (λ w : Circle =>
          (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
            (starRingEnd ℂ)
              (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
            (starRingEnd ℂ) (g w)) =
          fun w : Circle => (starRingEnd ℂ) (circleMap 0 1 theta ^ (k - j)) *
            ((w : ℂ) ^ (k - j) * (starRingEnd ℂ) (g w)) := by
        funext w
        rw [pow_mul_conj_pow_of_norm_one (hunit w) j k, if_neg hnle]
        simp only [map_pow, map_mul, starRingEnd_self_apply]
        rw [mul_pow]
        ring
      rw [hmuPoint, hnuPoint, integral_const_mul, integral_const_mul,
        integral_circle_pow_mul_conj_eq, integral_circle_pow_mul_conj_eq,
        hvanish (k - j), sub_self]

private theorem integrable_fejer_term_mul_conj
    (mu : Measure Circle) {f : Circle → ℂ} (hf : Integrable f mu)
    (theta : ℝ) (j k : ℕ) :
    Integrable (fun w : Circle =>
      (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
        (starRingEnd ℂ)
          (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
        (starRingEnd ℂ) (f w)) mu := by
  have hfc : Integrable (fun w : Circle => (starRingEnd ℂ) (f w)) mu :=
    (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hf
  refine hfc.bdd_mul (c := 1) (by fun_prop) ?_
  filter_upwards with w
  rw [norm_mul, norm_pow, norm_mul, norm_circleMap_zero]
  simp

private theorem integral_circleFejerKernelC_mul_conj
    (N : ℕ) (theta : ℝ) (mu : Measure Circle)
    {f : Circle → ℂ} (hf : Integrable f mu) :
    (∫ w, circleFejerKernelC N theta w * (starRingEnd ℂ) (f w) ∂mu) =
      ((N + 1 : ℂ)⁻¹) * ∑ j ∈ Finset.range (N + 1),
        ∑ k ∈ Finset.range (N + 1),
          ∫ w, ((((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
            (starRingEnd ℂ)
              (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
            (starRingEnd ℂ) (f w)) ∂mu := by
  have hpoint : (fun w : Circle =>
      circleFejerKernelC N theta w * (starRingEnd ℂ) (f w)) =
      fun w : Circle => ((N + 1 : ℂ)⁻¹) *
        ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          ((((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
            (starRingEnd ℂ)
              (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
            (starRingEnd ℂ) (f w)) := by
    funext w
    rw [circleFejerKernelC_eq_doubleSum, mul_assoc, Finset.sum_mul]
    simp_rw [Finset.sum_mul]
    apply congrArg (((N + 1 : ℂ)⁻¹) * .)
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    simp only [map_mul, map_pow]
    rw [mul_pow, mul_pow]
    ring
  rw [hpoint, integral_const_mul, integral_finsetSum]
  · apply congrArg (((N + 1 : ℂ)⁻¹) * .)
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum]
    intro k hk
    exact integrable_fejer_term_mul_conj mu hf theta j k
  · intro j hj
    apply integrable_finsetSum
    intro k hk
    exact integrable_fejer_term_mul_conj mu hf theta j k

/-- Boundary values of the analytic Fejer polynomial are exactly the conjugated-density
Fejer convolution. -/
theorem fAndMFejerPolynomial_eval_eq_kernel_integral
    (mu nu : Measure Circle) (f g : Circle → ℂ)
    (hf : Integrable f mu) (hg : Integrable g nu)
    (hvanish : ∀ n : ℕ,
      (∫ w, f w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂mu) =
        ∫ w, g w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂nu)
    (N : ℕ) (theta : ℝ) :
    (fAndMFejerPolynomial mu nu f g N).eval (circleMap 0 1 theta) =
      (∫ w, circleFejerKernelC N theta w * (starRingEnd ℂ) (f w) ∂mu) -
        ∫ w, circleFejerKernelC N theta w * (starRingEnd ℂ) (g w) ∂nu := by
  rw [fAndMFejerPolynomial_eval,
    integral_circleFejerKernelC_mul_conj N theta mu hf,
    integral_circleFejerKernelC_mul_conj N theta nu hg]
  symm
  calc
    ((N + 1 : ℂ)⁻¹ * ∑ j ∈ Finset.range (N + 1),
          ∑ k ∈ Finset.range (N + 1),
            ∫ w, ((((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
              (starRingEnd ℂ)
                (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
              (starRingEnd ℂ) (f w)) ∂mu) -
        ((N + 1 : ℂ)⁻¹ * ∑ j ∈ Finset.range (N + 1),
          ∑ k ∈ Finset.range (N + 1),
            ∫ w, ((((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
              (starRingEnd ℂ)
                (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
              (starRingEnd ℂ) (g w)) ∂nu) =
        ((N + 1 : ℂ)⁻¹ * ∑ j ∈ Finset.range (N + 1),
          ∑ k ∈ Finset.range (N + 1),
            ((∫ w, ((((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
              (starRingEnd ℂ)
                (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
              (starRingEnd ℂ) (f w)) ∂mu) -
             ∫ w, ((((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ j *
              (starRingEnd ℂ)
                (((circleMap 0 1 theta) * (starRingEnd ℂ) (w : ℂ)) ^ k)) *
              (starRingEnd ℂ) (g w)) ∂nu)) := by
          rw [← mul_sub]
          apply congrArg (((N + 1 : ℂ)⁻¹) * .)
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.sum_sub_distrib]
    _ = ((N + 1 : ℂ)⁻¹ * ∑ j ∈ Finset.range (N + 1),
          ∑ k ∈ Finset.range (N + 1),
            if k < j then circleMap 0 1 theta ^ (j - k) *
              (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g (j - k)) else 0) := by
        apply congrArg (((N + 1 : ℂ)⁻¹) * .)
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        exact integral_fejer_term_conj_sub mu nu f g hvanish theta j k
    _ = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          if k < j then ((N + 1 : ℂ)⁻¹ *
            (starRingEnd ℂ) (fAndMRemainingMoment mu nu f g (j - k))) *
              circleMap 0 1 theta ^ (j - k) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> ring

/-- Uniform `L¹` control of every finite analytic Fejer polynomial by the two density norms. -/
theorem polynomialBoundaryL1_fAndMFejerPolynomial_le
    (mu nu : Measure Circle) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (f g : Circle → ℂ) (hf : Integrable f mu) (hg : Integrable g nu)
    (hvanish : ∀ n : ℕ,
      (∫ w, f w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂mu) =
        ∫ w, g w * ((starRingEnd ℂ) (w : ℂ)) ^ n ∂nu)
    (N : ℕ) :
    polynomialBoundaryL1 (fAndMFejerPolynomial mu nu f g N) ≤
      (∫ w, ‖f w‖ ∂mu) + ∫ w, ‖g w‖ ∂nu := by
  let p := fAndMFejerPolynomial mu nu f g N
  let A : ℝ → ℝ := fun theta => ∫ w, circleFejerKernel N theta w * ‖f w‖ ∂mu
  let B : ℝ → ℝ := fun theta => ∫ w, circleFejerKernel N theta w * ‖g w‖ ∂nu
  have hpoint : ∀ theta : ℝ, ‖p.eval (circleMap 0 1 theta)‖ ≤ A theta + B theta := by
    intro theta
    rw [show p.eval (circleMap 0 1 theta) =
        (∫ w, circleFejerKernelC N theta w * (starRingEnd ℂ) (f w) ∂mu) -
          ∫ w, circleFejerKernelC N theta w * (starRingEnd ℂ) (g w) ∂nu from
      fAndMFejerPolynomial_eval_eq_kernel_integral mu nu f g hf hg hvanish N theta]
    calc
      ‖(∫ w, circleFejerKernelC N theta w * (starRingEnd ℂ) (f w) ∂mu) -
          ∫ w, circleFejerKernelC N theta w * (starRingEnd ℂ) (g w) ∂nu‖ ≤
          ‖∫ w, circleFejerKernelC N theta w * (starRingEnd ℂ) (f w) ∂mu‖ +
            ‖∫ w, circleFejerKernelC N theta w * (starRingEnd ℂ) (g w) ∂nu‖ :=
        norm_sub_le _ _
      _ ≤ (∫ w, ‖circleFejerKernelC N theta w * (starRingEnd ℂ) (f w)‖ ∂mu) +
          ∫ w, ‖circleFejerKernelC N theta w * (starRingEnd ℂ) (g w)‖ ∂nu :=
        add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
      _ = A theta + B theta := by
        apply congrArg₂ (fun a b : ℝ => a + b)
        · apply integral_congr_ae
          filter_upwards with w
          rw [circleFejerKernelC_eq_coe, norm_mul, norm_conj,
            Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (circleFejerKernel_nonneg N theta w)]
        · apply integral_congr_ae
          filter_upwards with w
          rw [circleFejerKernelC_eq_coe, norm_mul, norm_conj,
            Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (circleFejerKernel_nonneg N theta w)]
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpInt : IntervalIntegrable (fun theta => ‖p.eval (circleMap 0 1 theta)‖)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hAInt : IntervalIntegrable A volume 0 (2 * Real.pi) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hpi]
    exact (integrable_circleFejerKernel_mul_prod N mu hf.norm).integral_prod_left
  have hBInt : IntervalIntegrable B volume 0 (2 * Real.pi) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hpi]
    exact (integrable_circleFejerKernel_mul_prod N nu hg.norm).integral_prod_left
  have hABInt : IntervalIntegrable (fun theta => A theta + B theta)
      volume 0 (2 * Real.pi) := hAInt.add hBInt
  have hInt := intervalIntegral.integral_mono hpi hpInt hABInt hpoint
  rw [polynomialBoundaryL1]
  calc
    (2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..(2 * Real.pi),
        ‖p.eval (circleMap 0 1 theta)‖ ≤
        (2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..(2 * Real.pi),
          (A theta + B theta) := mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = ((2 * Real.pi)⁻¹ *
          (∫ theta in (0 : ℝ)..(2 * Real.pi), A theta)) +
        ((2 * Real.pi)⁻¹ *
          (∫ theta in (0 : ℝ)..(2 * Real.pi), B theta)) := by
      have hAdd : (∫ theta in (0 : ℝ)..(2 * Real.pi), (A theta + B theta)) =
          (∫ theta in (0 : ℝ)..(2 * Real.pi), A theta) +
            ∫ theta in (0 : ℝ)..(2 * Real.pi), B theta :=
        intervalIntegral.integral_add hAInt hBInt
      calc
        (2 * Real.pi)⁻¹ * ∫ theta in (0 : ℝ)..(2 * Real.pi), (A theta + B theta) =
            (2 * Real.pi)⁻¹ * ((∫ theta in (0 : ℝ)..(2 * Real.pi), A theta) +
              ∫ theta in (0 : ℝ)..(2 * Real.pi), B theta) :=
          congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hAdd
        _ = _ := mul_add _ _ _
    _ = (∫ w, ‖f w‖ ∂mu) + ∫ w, ‖g w‖ ∂nu := by
      simp only [A, B]
      rw [circleFejerKernel_integral_identity N mu hf.norm,
        circleFejerKernel_integral_identity N nu hg.norm]

end

end GaloisForLFunctions.HTGeometry
