import GaloisForLFunctions.SquareRootThreshold.HeightWindowAverageRepresentation

/-!
# The windowed mean value law: exactly diagonal below the window aperture

For a window `η` supported in `[-r, r]`, the height weight `|h_η(−2πξ)|²` is the Fourier transform
of `k_η = η ⋆ η̃`, which is supported in `[-2r, 2r]`. Let `Q(ξ) = Σ_j c_j e^{2πiξν_j}` be a finite
exponential sum.

* **Gram identity** (`integral_pairTransform_mul_normSq_expSum`):
  `∫ |h_η(−2πξ)|² |Q(ξ)|² dξ = Σ_{j,k} c_j c̄_k k_η(ν_j − ν_k)`.
* **Exact diagonal** (`integral_normSq_mul_normSq_expSum_of_separated`): if the frequencies are
  `2r`-separated, `∫ |h_η(−2πξ)|² |Q(ξ)|² dξ = ‖η‖² Σ_j |c_j|²`.

**Dirichlet polynomials** (`integral_normSq_mul_normSq_dirichletSum`). We have
`log m − log n ≥ 1/X` for `1 ≤ n < m ≤ X`. So if `2rX ≤ 1`, that is, if the height window has
length at least about twice the prime length, then every Dirichlet polynomial of length `X` is
seen exactly diagonally: `∫ |h_η(−2πξ)|² |Σ_{n ≤ X} c_n n^{2πiξ}|² dξ = ‖η‖² Σ |c_n|²`.

Below this threshold the off-diagonal of the windowed mean square vanishes identically. Above it,
the pairs `n ≠ m` with `|log(m/n)| < 2r` enter through `k_η(log(m/n))`. These are the shifted sums
that carry all the information beyond the square-root threshold.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-- A finite exponential sum `Q(ξ) = Σ_j c_j e^{2πiξν_j}`. -/
def expSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (ξ : ℝ) : ℂ :=
  ∑ j ∈ s, c j * cexp (2 * π * I * ξ * ν j)

theorem norm_cexp_two_pi_I_mul (ξ x : ℝ) : ‖cexp (2 * π * I * ξ * x)‖ = 1 := by
  rw [show (2 * π * I * ξ * x : ℂ) = ((2 * π * ξ * x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The Weil kernel of a window supported in `[-r, r]` vanishes at lags `|v| ≥ 2r`. -/
theorem weilTest_self_eq_zero_of_le {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) {v : ℝ} (hv : 2 * r ≤ |v|) : EF.weilTest η η v = 0 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hηs' : tsupport η ⊆ Icc (-(2 * r / 2)) (2 * r / 2) := by
    rwa [show 2 * r / 2 = r by ring]
  exact eq_zero_of_tsupport_subset_Icc (EF.weilTest_contDiff hη hη.continuous hηc).continuous
    (EF.tsupport_weilTest_subset hηs' hηs') hv

theorem weilTest_self_zero (η : ℝ → ℂ) :
    EF.weilTest η η 0 = ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) := by
  rw [weilTest_apply]
  simp only [sub_zero]
  exact integral_mul_conj_self_eq η

/-- **The windowed Gram identity.** -/
theorem integral_pairTransform_mul_normSq_expSum {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) :
    ∫ ξ : ℝ, pairTransform η ξ * (expSum s c ν ξ * conj (expSum s c ν ξ)) =
      ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) * EF.weilTest η η (ν j - ν k) := by
  obtain ⟨r, -, hsη⟩ := exists_radius_bound hηc
  have hPi := integrable_pairTransform hη hηc
  have hPc : Continuous fun ξ : ℝ => pairTransform η ξ :=
    (differentiable_pairTransform hη hηc).continuous.comp Complex.continuous_ofReal
  have he : ∀ ξ : ℝ, ∀ j k : ι, cexp (2 * π * I * ξ * ν j) * conj (cexp (2 * π * I * ξ * ν k)) =
      cexp (2 * π * I * ξ * ((ν j - ν k : ℝ) : ℂ)) := by
    intro ξ j k
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  have hexpand : ∀ ξ : ℝ, pairTransform η ξ * (expSum s c ν ξ * conj (expSum s c ν ξ)) =
      ∑ j ∈ s, ∑ k ∈ s, c j * conj (c k) *
        (pairTransform η ξ * cexp (2 * π * I * ξ * ((ν j - ν k : ℝ) : ℂ))) := by
    intro ξ
    have hQ : expSum s c ν ξ * conj (expSum s c ν ξ) = ∑ j ∈ s, ∑ k ∈ s,
        c j * conj (c k) * cexp (2 * π * I * ξ * ((ν j - ν k : ℝ) : ℂ)) := by
      simp only [expSum, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [← he ξ j k]
      ring
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hint : ∀ j k : ι, Integrable fun ξ : ℝ => c j * conj (c k) *
      (pairTransform η ξ * cexp (2 * π * I * ξ * ((ν j - ν k : ℝ) : ℂ))) := by
    intro j k
    refine Integrable.const_mul (hPi.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)) _
    · exact (hPc.mul (by fun_prop)).aestronglyMeasurable
    · rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one]
  rw [integral_congr_ae (Eventually.of_forall hexpand),
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hint j k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, ← weilTest_eq_integral hη hηc hsη]

/-- **The windowed mean value law at separated frequencies** (complex form). -/
theorem integral_pairTransform_mul_normSq_expSum_of_separated {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ)
    (hsep : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → 2 * r ≤ |ν j - ν k|) :
    ∫ ξ : ℝ, pairTransform η ξ * (expSum s c ν ξ * conj (expSum s c ν ξ)) =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ∑ j ∈ s, ((‖c j‖ ^ 2 : ℝ) : ℂ) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  rw [integral_pairTransform_mul_normSq_expSum hη hηc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_eq_single j]
  · rw [sub_self, weilTest_self_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  · intro k hk hkj
    rw [weilTest_self_eq_zero_of_le hη hηs (hsep j hj k hk (Ne.symm hkj)), mul_zero]
  · intro hj'
    exact absurd hj hj'

/-- **The windowed mean value law at separated frequencies.** For a window supported in
`[-r, r]` and `2r`-separated frequencies,
`∫ |h_η(−2πξ)|² |Σ_j c_j e^{2πiξν_j}|² dξ = ‖η‖² Σ_j |c_j|²`. -/
theorem integral_normSq_mul_normSq_expSum_of_separated {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    {r : ℝ} (hηs : tsupport η ⊆ Icc (-r) r) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ)
    (hsep : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → 2 * r ≤ |ν j - ν k|) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖expSum s c ν ξ‖ ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * ∑ j ∈ s, ‖c j‖ ^ 2 := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have h := integral_pairTransform_mul_normSq_expSum_of_separated hη hηs s c ν hsep
  have hfun : (fun ξ : ℝ => pairTransform η ξ * (expSum s c ν ξ * conj (expSum s c ν ξ))) =
      fun ξ : ℝ => ((‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 * ‖expSum s c ν ξ‖ ^ 2 : ℝ) : ℂ) := by
    funext ξ
    rw [pairTransform_ofReal hη hηc ξ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hfun, integral_complex_ofReal] at h
  exact_mod_cast h

/-- Logarithms of integers up to `X` are `1/X`-separated. -/
theorem inv_le_log_sub_log {n m : ℕ} {X : ℝ} (hn : 1 ≤ n) (hnm : n < m) (hmX : (m : ℝ) ≤ X) :
    1 / X ≤ Real.log m - Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le n) hnm)
  have hnm' : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hm0 hn0)
  rw [Real.log_div hm0.ne' hn0.ne', inv_div] at hlog
  have h1 : 1 / X ≤ 1 / (m : ℝ) := one_div_le_one_div_of_le hm0 hmX
  have h2 : 1 / (m : ℝ) ≤ 1 - n / m := by
    rw [one_sub_div hm0.ne', div_le_div_iff_of_pos_right hm0]
    linarith
  linarith

/-- **Dirichlet polynomials below the window length are seen exactly diagonally.** For a window
supported in `[-r, r]` with `2rX ≤ 1` and coefficients on `1 ≤ n ≤ X`,
`∫ |h_η(−2πξ)|² |Σ_n c_n n^{2πiξ}|² dξ = ‖η‖² Σ_n |c_n|²`. -/
theorem integral_normSq_mul_normSq_dirichletSum {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r X : ℝ}
    (hr : 0 ≤ r) (hηs : tsupport η ⊆ Icc (-r) r) (hX : 2 * r * X ≤ 1) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ X) (c : ℕ → ℂ) :
    ∫ ξ : ℝ, ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖expSum s c (fun n => Real.log n) ξ‖ ^ 2 =
      (∫ t, ‖η t‖ ^ 2) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  refine integral_normSq_mul_normSq_expSum_of_separated hη hηs s c _ fun n hn m hm hnm => ?_
  have hX0 : 0 < X := lt_of_lt_of_le one_pos (le_trans (by exact_mod_cast (hs n hn).1) (hs n hn).2)
  have h2r : 2 * r ≤ 1 / X := by rw [le_div_iff₀ hX0]; exact hX
  rcases lt_or_gt_of_ne hnm with h | h
  · have := inv_le_log_sub_log (hs n hn).1 h (hs m hm).2
    rw [abs_sub_comm, abs_of_nonneg (by linarith [div_pos one_pos hX0])]
    linarith
  · have := inv_le_log_sub_log (hs m hm).1 h (hs n hn).2
    rw [abs_of_nonneg (by linarith [div_pos one_pos hX0])]
    linarith

end GaloisForLFunctions.SquareRootThreshold
