import GaloisForLFunctions.HTGeometry.KroneckerFlowDensity

/-!
# Discrete averages of the cosine-power kernel along a rotation orbit

For `α : d → ℝ` and the kernel `K(n) = Π_i cos(π n α_i)^{2M}`, the averages
`(1/N) Σ_{n<N} K(n)` approach the resonant mass `Σ_{ω_J ∈ ℤ} C_J ≥ (2M+1)^{−d}` at rate
`O(1/N)` (`exists_discreteKernel_average`). Here `ω_J = Σ_i α_i(J_i − M)` and `C_J` are the
binomial kernel coefficients. Every frequency with `ω_J ∉ ℤ` gives a geometric sum with ratio
`e^{2πiω_J} ≠ 1`, and every frequency with `ω_J ∈ ℤ` is constant along the integers. No relation
hypothesis is needed because the target is the origin.

**Consequence** (`exists_bohr_return_density`). For every `ε > 0` the integers `n` with all
`nα_i` within `ε` of `ℤ` have positive lower density: for some `c > 0` and all large `N`, at least
`cN` of the `n < N` qualify. More precisely, the kernel average already gives the weighted form
used by consumers (`exists_kernel_return_mass`).
-/

open Complex Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.KroneckerFlow

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Discrete kernel averages.** -/
theorem exists_discreteKernel_average (M : ℕ) (α : d → ℝ) :
    ∃ a₀ E : ℝ, (1 / ((2 * M + 1 : ℕ) : ℝ)) ^ Fintype.card d ≤ a₀ ∧ 0 ≤ E ∧
      ∀ N : ℕ, 0 < N →
        |(∑ n ∈ Finset.range N, flowKernel M α 0 n) / N - a₀| ≤ E / N := by
  classical
  set J₀ : d → Fin (2 * M + 1) := fun _ => ⟨M, by omega⟩ with hJ₀
  set ω : (d → Fin (2 * M + 1)) → ℝ := fun J => ∑ i, α i * (((J i : ℕ) : ℝ) - M) with hω
  set R : (d → Fin (2 * M + 1)) → Prop := fun J => ∃ z : ℤ, ω J = z with hR
  have hω₀ : R J₀ := ⟨0, by simp [hω, hJ₀]⟩
  set w : (d → Fin (2 * M + 1)) → ℂ := fun J => Complex.exp (2 * Real.pi * I * ω J) with hw
  have hwnorm : ∀ J, ‖w J‖ = 1 := by
    intro J
    rw [hw, Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hwR : ∀ J, R J → w J = 1 := by
    intro J ⟨z, hz⟩
    show Complex.exp (2 * Real.pi * I * ((ω J : ℝ) : ℂ)) = 1
    rw [hz]
    rw [show (2 * Real.pi * I * ((z : ℝ) : ℂ)) = (z : ℂ) * (2 * Real.pi * I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I z
  have hw1 : ∀ J, ¬ R J → w J ≠ 1 := by
    intro J hJ h1
    apply hJ
    rw [hw, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : ((ω J : ℝ) : ℂ) = n := by
      apply mul_left_cancel₀ hpi
      rw [show 2 * Real.pi * I * ((ω J : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi * I) from hn]
      ring
    exact_mod_cast h2
  set C : (d → Fin (2 * M + 1)) → ℝ := fun J => ∏ i, cosKernelCoeff M (J i) with hC
  have hC0 : ∀ J, 0 ≤ C J := fun J => Finset.prod_nonneg fun i _ => cosKernelCoeff_nonneg M _
  refine ⟨∑ J ∈ univ.filter R, C J, ∑ J ∈ univ.filter (fun J => ¬ R J), C J * (2 / ‖w J - 1‖),
    ?_, Finset.sum_nonneg fun J _ => mul_nonneg (hC0 J) (by positivity), ?_⟩
  · refine le_trans ?_ (Finset.single_le_sum (f := C) (fun J _ => hC0 J)
      (Finset.mem_filter.mpr ⟨mem_univ _, hω₀⟩))
    rw [hC]
    simp only [hJ₀]
    rw [Finset.prod_const, Finset.card_univ]
    apply pow_le_pow_left₀ (by positivity)
    have := cosKernelCoeff_middle_ge M
    push_cast
    exact this
  intro N hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hexp : ∀ n : ℕ, ((flowKernel M α 0 n : ℝ) : ℂ) = ∑ J, (C J : ℂ) * w J ^ n := by
    intro n
    rw [flowKernel, prod_cos_pow_eq_sum M (fun i => (n : ℝ) * α i - (0 : d → ℝ) i)]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hw, ← Complex.exp_nat_mul]
    congr 2
    simp only [hω, Pi.zero_apply, sub_zero]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  -- the complex average
  have hcx : ‖((∑ n ∈ Finset.range N, flowKernel M α 0 n : ℝ) : ℂ) / N -
      ((∑ J ∈ univ.filter R, C J : ℝ) : ℂ)‖ ≤
      (∑ J ∈ univ.filter (fun J => ¬ R J), C J * (2 / ‖w J - 1‖)) / N := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl fun n _ => hexp n, Finset.sum_comm,
      ← Finset.sum_filter_add_sum_filter_not univ R]
    rw [show (∑ J ∈ univ.filter R, ∑ n ∈ Finset.range N, (C J : ℂ) * w J ^ n) =
        (N : ℂ) * ((∑ J ∈ univ.filter R, C J : ℝ) : ℂ) by
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [hwR J (Finset.mem_filter.mp hJ).2]
      simp only [one_pow, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
    rw [add_div, mul_div_cancel_left₀ _ hNc, add_sub_cancel_left, norm_div, Complex.norm_natCast,
      div_le_div_iff_of_pos_right (by exact_mod_cast hN)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun J hJ => ?_)
    have hJne : ¬ R J := (Finset.mem_filter.mp hJ).2
    rw [← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hC0 J)]
    exact mul_le_mul_of_nonneg_left (norm_unit_geom_sum_le (hwnorm J) (hw1 J hJne) N) (hC0 J)
  have hre : ((∑ n ∈ Finset.range N, flowKernel M α 0 n : ℝ) : ℂ) / N -
      ((∑ J ∈ univ.filter R, C J : ℝ) : ℂ) =
      (((∑ n ∈ Finset.range N, flowKernel M α 0 n) / N - ∑ J ∈ univ.filter R, C J : ℝ) : ℂ) := by
    push_cast; ring
  rw [hre, Complex.norm_real, Real.norm_eq_abs] at hcx
  exact hcx

omit [DecidableEq d] in
theorem flowKernel_nonneg (M : ℕ) (α x : d → ℝ) (t : ℝ) : 0 ≤ flowKernel M α x t := by
  unfold flowKernel
  exact Finset.prod_nonneg fun i _ => by rw [pow_mul]; positivity

omit [DecidableEq d] in
theorem flowKernel_le_one (M : ℕ) (α x : d → ℝ) (t : ℝ) : flowKernel M α x t ≤ 1 := by
  unfold flowKernel
  apply Finset.prod_le_one (fun i _ => by rw [pow_mul]; positivity)
  intro i _
  rw [pow_mul]
  apply pow_le_one₀ (sq_nonneg _)
  rw [sq_le_one_iff_abs_le_one]
  exact Real.abs_cos_le_one _

open scoped Classical in
/-- **Kernel mass on the return set.** For every `ε ∈ (0, ¼]` there are a kernel order `M` and a
mass `a > 0` such that, for all large `N`, `Σ_{n<N, n ∈ B_ε} K(n) ≥ aN`, where
`B_ε = {n : ∀ i, ∃ z, |nα_i − z| < ε}` and `0 ≤ K ≤ 1` vanishes to order `cos(πε)^{2M}` off
`B_ε`. -/
theorem exists_kernel_return_mass (α : d → ℝ) {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ M : ℕ, ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
      a * N ≤ ∑ n ∈ (Finset.range N).filter
        (fun n : ℕ => ∀ i, ∃ z : ℤ, |(n : ℝ) * α i - 0 - z| < ε), flowKernel M α 0 n := by
  classical
  set c : ℝ := Real.cos (Real.pi * ε) with hc
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hc1 : c < 1 := by
    rw [hc]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl 0)
      (show Real.pi * ε ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
      (show 0 < Real.pi * ε by positivity)
    rwa [Real.cos_zero] at h
  obtain ⟨M, hMbound⟩ := exists_kernel_order (Fintype.card d) hc0 hc1
  obtain ⟨a₀, E, ha₀, hE0, havg⟩ := exists_discreteKernel_average M α
  have hpow : 0 < ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d := by positivity
  have hcM : c ^ (2 * M) < a₀ / 2 := by
    have h2 : (1 / ((2 * M + 1 : ℕ) : ℝ)) ^ Fintype.card d =
        1 / ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d := by rw [one_div_pow]
    rw [h2] at ha₀
    have : c ^ (2 * M) < 1 / 2 / ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d := by
      rw [lt_div_iff₀ hpow]; linarith
    calc c ^ (2 * M) < 1 / 2 / ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d := this
      _ = (1 / ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d) / 2 := by ring
      _ ≤ a₀ / 2 := by linarith
  have ha₀pos : 0 < a₀ := lt_of_le_of_lt (by positivity) (by linarith [hcM, pow_pos hc0 (2 * M)] :
    (0 : ℝ) < a₀)
  set a : ℝ := a₀ / 2 - c ^ (2 * M) with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * E / a)
  refine ⟨M, a / 2, by linarith, N₀, fun N hN hN0 => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have h1 := havg N hN0
  rw [abs_le] at h1
  have hsum_lower : (a₀ - E / N) * N ≤ ∑ n ∈ Finset.range N, flowKernel M α 0 n := by
    have := h1.1
    rw [le_sub_iff_add_le, le_div_iff₀ hNr] at this
    nlinarith
  -- off the return set the kernel is small
  have hoff : ∑ n ∈ (Finset.range N).filter
      (fun n : ℕ => ¬ ∀ i, ∃ z : ℤ, |(n : ℝ) * α i - 0 - z| < ε), flowKernel M α 0 n ≤
      N * c ^ (2 * M) := by
    calc ∑ n ∈ (Finset.range N).filter
          (fun n : ℕ => ¬ ∀ i, ∃ z : ℤ, |(n : ℝ) * α i - 0 - z| < ε), flowKernel M α 0 n
        ≤ ∑ n ∈ (Finset.range N).filter
          (fun n : ℕ => ¬ ∀ i, ∃ z : ℤ, |(n : ℝ) * α i - 0 - z| < ε), c ^ (2 * M) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hnot := (Finset.mem_filter.mp hn).2
          push Not at hnot
          obtain ⟨i₀, hi₀⟩ := hnot
          exact flowKernel_le_of_far M α 0 hε.le (i₀ := i₀) fun z => by
            simpa using hi₀ z
      _ ≤ ∑ _n ∈ Finset.range N, c ^ (2 * M) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
      _ = N * c ^ (2 * M) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n : ℕ => ∀ i, ∃ z : ℤ, |(n : ℝ) * α i - 0 - z| < ε) (fun n => flowKernel M α 0 n)
  have hNbig : 2 * E / a < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
  have hEN : E ≤ a / 2 * N := by
    rw [div_lt_iff₀ ha0] at hNbig
    linarith
  have hEdiv : E / N * N = E := by field_simp
  nlinarith

end

end GaloisForLFunctions.HTGeometry.KroneckerFlow
