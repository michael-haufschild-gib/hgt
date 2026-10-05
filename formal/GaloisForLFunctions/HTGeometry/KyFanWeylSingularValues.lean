import GaloisForLFunctions.HTGeometry.SingularValues
import GaloisForLFunctions.RHTower.SchattenTwoIdentity

/-!
# The Ky Fan maximum principle and Weyl's inequality for compact operators

For a compact operator `T` on a complex Hilbert space with approximation numbers
(= singular values) `a_j(T)`, put `K_N(T) = Σ_{j<N} a_j(T)`.

* **Ky Fan maximum principle.**  For orthonormal `u_1, …, u_r`, `v_1, …, v_r` with `r ≤ N`,
  `Σ_k |⟨v_k, T u_k⟩| ≤ K_N(T)`, and some such families attain `K_N(T)`.  The proof expands
  `T = Σ_j s_j ⟨e_j, ·⟩ f_j` along the greedy singular system and uses the elementary
  rearrangement bound `Σ_j s_j c_j ≤ Σ_{j<N} s_j` for `0 ≤ c_j ≤ 1`, `Σ c_j ≤ N`.
* **Ky Fan's inequality** `K_N(A + B) ≤ K_N(A) + K_N(B)`.
* **Weyl's inequality.**  For distinct `μ_i` with finite-dimensional generalized eigenspaces and
  `m_i ≤ dim G(T, μ_i)`, `Σ m_i |μ_i| ≤ K_{Σ m_i}(T)`.  An orthonormal Schur flag is built inside
  `⊕ G(T, μ_i)`: each new unit vector `x` is orthogonal to the current invariant span `W` and has
  `(T − μ)x ∈ W`, so `⟨x, T x⟩ = μ`.
-/

open scoped InnerProductSpace ComplexConjugate
open Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Ky Fan partial sum `K_N(T) = Σ_{j<N} a_j(T)`. -/
def kyFanSum (T : H →L[ℂ] H) (N : ℕ) : ℝ := ∑ j ∈ range N, approxNumber T j

omit [CompleteSpace H] in
theorem kyFanSum_nonneg (T : H →L[ℂ] H) (N : ℕ) : 0 ≤ kyFanSum T N :=
  sum_nonneg fun j _ => approxNumber_nonneg T j

omit [CompleteSpace H] in
theorem kyFanSum_mono (T : H →L[ℂ] H) {M N : ℕ} (h : M ≤ N) : kyFanSum T M ≤ kyFanSum T N :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) fun j _ _ => approxNumber_nonneg T j

omit [CompleteSpace H] in
theorem kyFanSum_le_mul_norm (T : H →L[ℂ] H) (N : ℕ) : kyFanSum T N ≤ N * ‖T‖ := by
  refine (sum_le_card_nsmul _ _ _ fun j _ => approxNumber_le_norm T j).trans (le_of_eq ?_)
  rw [card_range, nsmul_eq_mul]

/-! ## The rearrangement bound -/

/-- `Σ_{j<M} s_j c_j ≤ Σ_{j<N} s_j` for `s` antitone nonnegative and `0 ≤ c_j ≤ 1`,
`Σ_{j<M} c_j ≤ N`. -/
theorem sum_mul_le_sum_range_of_antitone {s : ℕ → ℝ} (hs : Antitone s) (hs0 : ∀ j, 0 ≤ s j)
    {c : ℕ → ℝ} (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) {M N : ℕ}
    (hsum : ∑ j ∈ range M, c j ≤ N) : ∑ j ∈ range M, s j * c j ≤ ∑ j ∈ range N, s j := by
  rcases le_or_gt M N with hMN | hNM
  · calc ∑ j ∈ range M, s j * c j ≤ ∑ j ∈ range M, s j :=
          sum_le_sum fun j _ => by nlinarith [hs0 j, hc1 j]
      _ ≤ ∑ j ∈ range N, s j :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hMN) fun j _ _ => hs0 j
  · have hsplit : ∑ j ∈ range M, s j * c j =
        ∑ j ∈ range N, s j * c j + ∑ j ∈ Ico N M, s j * c j := by
      rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le N) hNM.le, range_eq_Ico]
    have hcsplit : ∑ j ∈ range M, c j = ∑ j ∈ range N, c j + ∑ j ∈ Ico N M, c j := by
      rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le N) hNM.le, range_eq_Ico]
    have h1 : ∑ j ∈ Ico N M, s j * c j ≤ s N * ∑ j ∈ Ico N M, c j := by
      rw [mul_sum]
      exact sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hs (mem_Ico.1 hj).1) (hc0 j)
    have h2 : s N * ∑ j ∈ range N, (1 - c j) ≤ ∑ j ∈ range N, s j * (1 - c j) := by
      rw [mul_sum]
      exact sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (hs (mem_range.1 hj).le) (by linarith [hc1 j])
    have h3 : ∑ j ∈ range N, (1 - c j) = N - ∑ j ∈ range N, c j := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    have h4 : ∑ j ∈ range N, s j * (1 - c j) = ∑ j ∈ range N, s j - ∑ j ∈ range N, s j * c j := by
      rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
    have hsN := hs0 N
    rw [hsplit]
    nlinarith

/-! ## Bessel for orthonormal-or-zero families -/

omit [CompleteSpace H] in
theorem sum_norm_inner_sq_le_of_orthogonal {w : ℕ → H} (hw : ∀ i j, i ≠ j → ⟪w i, w j⟫_ℂ = 0)
    (hw1 : ∀ j, w j = 0 ∨ ‖w j‖ = 1) (s : Finset ℕ) (x : H) :
    ∑ j ∈ s, ‖⟪w j, x⟫_ℂ‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  set s' := s.filter (fun j => w j ≠ 0)
  have hsum : ∑ j ∈ s, ‖⟪w j, x⟫_ℂ‖ ^ 2 = ∑ j ∈ s', ‖⟪w j, x⟫_ℂ‖ ^ 2 := by
    rw [sum_filter]
    refine sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · push Not at h; simp [h]
  have hon : Orthonormal ℂ (fun j : s' => w j) := by
    refine ⟨fun j => ?_, fun i j hij => hw i j fun h => hij (Subtype.ext h)⟩
    rcases hw1 j with h | h
    · exact absurd h (mem_filter.1 j.2).2
    · exact h
  have h := hon.sum_inner_products_le (s := Finset.univ) (x := x)
  rw [hsum, ← sum_coe_sort s']
  exact h

/-! ## The singular system of a compact operator -/

section SingularSystem

variable {T : H →L[ℂ] H} (hT : IsCompactOperator T)
include hT

theorem svVec_energyOp_eq_zero_or_norm_eq_one (j : ℕ) :
    svVec (energyOp T) j = 0 ∨ ‖svVec (energyOp T) j‖ = 1 := by
  by_cases h : svVal (energyOp T) j = 0
  · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ h)
  · exact Or.inr (norm_svVec_of_ne_zero (energyOp_compact hT) (energyOp_symmetric T)
      (energyOp_pos T) h)

omit hT in
theorem norm_apply_svVec_energyOp (j : ℕ) :
    ‖T (svVec (energyOp T) j)‖ = singVal T j * ‖svVec (energyOp T) j‖ := by
  have h := norm_apply_svVec_sq T j
  rw [← singVal_sq, ← mul_pow] at h
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (singVal_nonneg T j) (norm_nonneg _))
    two_ne_zero).1 h

omit hT in
theorem singVal_ne_zero_iff (j : ℕ) : singVal T j ≠ 0 ↔ svVal (energyOp T) j ≠ 0 := by
  rw [singVal, Ne, Real.sqrt_eq_zero (svVal_nonneg _ j)]

theorem norm_svVec_energyOp_of_singVal_ne_zero {j : ℕ} (hj : singVal T j ≠ 0) :
    ‖svVec (energyOp T) j‖ = 1 :=
  norm_svVec_of_ne_zero (energyOp_compact hT) (energyOp_symmetric T) (energyOp_pos T)
    ((singVal_ne_zero_iff j).1 hj)

/-- The left singular vectors `f_j = s_j⁻¹ T e_j`. -/
def leftSingularVec (T : H →L[ℂ] H) (j : ℕ) : H := ((singVal T j : ℂ)⁻¹) • T (svVec (energyOp T) j)

omit hT in
theorem inner_apply_svVec_apply_svVec_of_ne {i j : ℕ} (h : i ≠ j) :
    ⟪T (svVec (energyOp T) i), T (svVec (energyOp T) j)⟫_ℂ = 0 := by
  rw [← adjoint_inner_right, ← comp_apply, show adjoint T ∘L T = energyOp T from rfl, apply_svVec,
    inner_smul_right, inner_svVec_svVec_of_ne _ h, mul_zero]

omit hT in
theorem apply_svVec_eq_smul_leftSingularVec (j : ℕ) :
    T (svVec (energyOp T) j) = (singVal T j : ℂ) • leftSingularVec T j := by
  rw [leftSingularVec, smul_smul]
  by_cases h : singVal T j = 0
  · have hz : T (svVec (energyOp T) j) = 0 := by
      rw [← norm_eq_zero, norm_apply_svVec_energyOp, h, zero_mul]
    rw [hz, smul_zero]
  · rw [mul_inv_cancel₀ (by exact_mod_cast h), one_smul]

omit hT in
theorem leftSingularVec_orthogonal {i j : ℕ} (h : i ≠ j) :
    ⟪leftSingularVec T i, leftSingularVec T j⟫_ℂ = 0 := by
  rw [leftSingularVec, leftSingularVec, inner_smul_left, inner_smul_right,
    inner_apply_svVec_apply_svVec_of_ne h, mul_zero, mul_zero]

theorem leftSingularVec_eq_zero_or_norm_eq_one (j : ℕ) :
    leftSingularVec T j = 0 ∨ ‖leftSingularVec T j‖ = 1 := by
  by_cases h : singVal T j = 0
  · left; rw [leftSingularVec, h]; simp
  · right
    have hs := singVal_nonneg T j
    rw [leftSingularVec, norm_smul, norm_apply_svVec_energyOp,
      norm_svVec_energyOp_of_singVal_ne_zero hT h, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs, mul_one, inv_mul_cancel₀ h]

omit hT in
theorem inner_svVec_energyOp_orthogonal {i j : ℕ} (h : i ≠ j) :
    ⟪svVec (energyOp T) i, svVec (energyOp T) j⟫_ℂ = 0 :=
  inner_svVec_svVec_of_ne _ h

theorem tendsto_singVal : Tendsto (singVal T) atTop (𝓝 0) := by
  have h := svVal_tendsto_zero (energyOp_compact hT) (energyOp_symmetric T) (energyOp_pos T)
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h
  rwa [Real.sqrt_zero] at h2

/-- The truncated singular expansion converges: `Σ_{j<M} ⟨e_j, x⟩ T e_j → T x`. -/
theorem tendsto_sum_inner_svVec_smul_apply (x : H) :
    Tendsto (fun M => ∑ j ∈ range M, ⟪svVec (energyOp T) j, x⟫_ℂ • T (svVec (energyOp T) j))
      atTop (𝓝 (T x)) := by
  set e := svVec (energyOp T)
  set xM : ℕ → H := fun M => ∑ j ∈ range M, ⟪e j, x⟫_ℂ • e j
  have horth : ∀ M, ∀ m < M, ⟪e m, x - xM M⟫_ℂ = 0 := by
    intro M m hm
    rw [inner_sub_right, inner_sum, sum_eq_single m]
    · rw [inner_smul_right]
      rcases svVec_energyOp_eq_zero_or_norm_eq_one hT m with h | h
      · simp [e, h]
      · rw [inner_self_eq_norm_sq_to_K, h]; simp
    · intro j _ hjm
      rw [inner_smul_right, inner_svVec_energyOp_orthogonal (Ne.symm hjm), mul_zero]
    · intro hm'; exact absurd (mem_range.2 hm) hm'
  have hnorm : ∀ M, ‖x - xM M‖ ≤ ‖x‖ := by
    intro M
    have hperp : ⟪xM M, x - xM M⟫_ℂ = 0 := by
      simp only [xM]
      rw [sum_inner]
      exact sum_eq_zero fun j hj => by rw [inner_smul_left, horth M j (mem_range.1 hj), mul_zero]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (xM M) (x - xM M) hperp
    rw [add_sub_cancel] at hpy
    nlinarith [norm_nonneg (xM M), norm_nonneg (x - xM M), norm_nonneg x]
  have hbound : ∀ M, ‖T x - ∑ j ∈ range M, ⟪e j, x⟫_ℂ • T (e j)‖ ≤ singVal T M * ‖x‖ := by
    intro M
    have hTx : ∑ j ∈ range M, ⟪e j, x⟫_ℂ • T (e j) = T (xM M) := by
      simp only [xM, map_sum, map_smul]
    rw [hTx, ← map_sub]
    exact (norm_apply_le_singVal_of_orth T M (horth M)).trans
      (mul_le_mul_of_nonneg_left (hnorm M) (singVal_nonneg T M))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun M => singVal T M * ‖x‖) (fun M => norm_nonneg _) (fun M => ?_) ?_
  · rw [norm_sub_rev]; exact hbound M
  · simpa using (tendsto_singVal hT).mul_const ‖x‖

end SingularSystem

/-! ## The Ky Fan maximum principle -/

theorem approxNumber_eq_singVal' {T : H →L[ℂ] H} (hT : IsCompactOperator T) (j : ℕ) :
    approxNumber T j = singVal T j := approxNumber_eq_singVal hT j

/-- **Ky Fan maximum principle (upper bound).**  For orthonormal `u, v : Fin r → H`, `r ≤ N`,
`Σ_k |⟨v_k, T u_k⟩| ≤ K_N(T)`. -/
theorem sum_norm_inner_le_kyFanSum {T : H →L[ℂ] H} (hT : IsCompactOperator T) {r N : ℕ} (hr : r ≤ N)
    {u v : Fin r → H} (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) :
    ∑ k, ‖⟪v k, T (u k)⟫_ℂ‖ ≤ kyFanSum T N := by
  set e := svVec (energyOp T)
  set f := leftSingularVec T
  set s := singVal T
  set a : ℕ → Fin r → ℝ := fun j k => ‖⟪e j, u k⟫_ℂ‖
  set b : ℕ → Fin r → ℝ := fun j k => ‖⟪f j, v k⟫_ℂ‖
  -- the truncated quantities
  set F : ℕ → ℝ := fun M => ∑ k, ‖⟪v k, ∑ j ∈ range M, ⟪e j, u k⟫_ℂ • T (e j)⟫_ℂ‖
  have hlim : Tendsto F atTop (𝓝 (∑ k, ‖⟪v k, T (u k)⟫_ℂ‖)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    exact ((continuous_inner.comp (continuous_const.prodMk continuous_id)).tendsto _ |>.comp
      (tendsto_sum_inner_svVec_smul_apply hT (u k))).norm
  have hab : ∀ j k, ‖⟪v k, ⟪e j, u k⟫_ℂ • T (e j)⟫_ℂ‖ = s j * (a j k * b j k) := by
    intro j k
    rw [apply_svVec_eq_smul_leftSingularVec, inner_smul_right, inner_smul_right, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (singVal_nonneg T j), norm_inner_symm (v k)]
    simp only [a, b, f, s]
    ring
  have hbessel_e : ∀ k (M : ℕ), ∑ j ∈ range M, a j k ^ 2 ≤ 1 := by
    intro k M
    have := sum_norm_inner_sq_le_of_orthogonal (w := e)
      (fun i j h => inner_svVec_energyOp_orthogonal h)
      (svVec_energyOp_eq_zero_or_norm_eq_one hT) (range M) (u k)
    rwa [hu.1 k, one_pow] at this
  have hbessel_f : ∀ k (M : ℕ), ∑ j ∈ range M, b j k ^ 2 ≤ 1 := by
    intro k M
    have := sum_norm_inner_sq_le_of_orthogonal (w := f)
      (fun i j h => leftSingularVec_orthogonal h)
      (leftSingularVec_eq_zero_or_norm_eq_one hT) (range M) (v k)
    rwa [hv.1 k, one_pow] at this
  have hbessel_u : ∀ j, ∑ k, a j k ^ 2 ≤ 1 := by
    intro j
    have h := hu.sum_inner_products_le (s := Finset.univ) (x := e j)
    have he : ‖e j‖ ^ 2 ≤ 1 := by
      rcases svVec_energyOp_eq_zero_or_norm_eq_one hT j with h0 | h1
      · simp [e, h0]
      · rw [h1]; norm_num
    refine le_trans (le_of_eq ?_) (h.trans he)
    exact sum_congr rfl fun k _ => by simp only [a]; rw [norm_inner_symm]
  have hbessel_v : ∀ j, ∑ k, b j k ^ 2 ≤ 1 := by
    intro j
    have h := hv.sum_inner_products_le (s := Finset.univ) (x := f j)
    have hf : ‖f j‖ ^ 2 ≤ 1 := by
      rcases leftSingularVec_eq_zero_or_norm_eq_one hT j with h0 | h1
      · simp [f, h0]
      · rw [h1]; norm_num
    refine le_trans (le_of_eq ?_) (h.trans hf)
    exact sum_congr rfl fun k _ => by simp only [b]; rw [norm_inner_symm]
  have hFM : ∀ M, F M ≤ kyFanSum T N := by
    intro M
    set c : ℕ → ℝ := fun j => ∑ k, a j k * b j k
    have hc0 : ∀ j, 0 ≤ c j := fun j => sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hamgm : ∀ j k, a j k * b j k ≤ (a j k ^ 2 + b j k ^ 2) / 2 := fun j k => by
      nlinarith [sq_nonneg (a j k - b j k)]
    have hc1 : ∀ j, c j ≤ 1 := by
      intro j
      calc c j ≤ ∑ k, (a j k ^ 2 + b j k ^ 2) / 2 := sum_le_sum fun k _ => hamgm j k
        _ = (∑ k, a j k ^ 2 + ∑ k, b j k ^ 2) / 2 := by rw [← sum_div, sum_add_distrib]
        _ ≤ 1 := by linarith [hbessel_u j, hbessel_v j]
    have hcsum : ∑ j ∈ range M, c j ≤ N := by
      calc ∑ j ∈ range M, c j = ∑ k, ∑ j ∈ range M, a j k * b j k := by
            simp only [c]; rw [sum_comm]
        _ ≤ ∑ k : Fin r, (1 : ℝ) := by
            refine sum_le_sum fun k _ => ?_
            calc ∑ j ∈ range M, a j k * b j k ≤ ∑ j ∈ range M, (a j k ^ 2 + b j k ^ 2) / 2 :=
                  sum_le_sum fun j _ => hamgm j k
              _ = (∑ j ∈ range M, a j k ^ 2 + ∑ j ∈ range M, b j k ^ 2) / 2 := by
                  rw [← sum_div, sum_add_distrib]
              _ ≤ 1 := by linarith [hbessel_e k M, hbessel_f k M]
        _ = r := by simp
        _ ≤ N := by exact_mod_cast hr
    calc F M ≤ ∑ k, ∑ j ∈ range M, ‖⟪v k, ⟪e j, u k⟫_ℂ • T (e j)⟫_ℂ‖ := by
          refine sum_le_sum fun k _ => ?_
          rw [inner_sum]
          exact norm_sum_le _ _
      _ = ∑ j ∈ range M, s j * c j := by
          simp_rw [hab]
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          simp only [c]; rw [mul_sum]
      _ ≤ ∑ j ∈ range N, s j :=
          sum_mul_le_sum_range_of_antitone (singVal_antitone T) (singVal_nonneg T) hc0 hc1 hcsum
      _ = kyFanSum T N := by
          rw [kyFanSum]; exact sum_congr rfl fun j _ => (approxNumber_eq_singVal hT j).symm
  exact le_of_tendsto' hlim hFM

/-- **Ky Fan maximum principle (attainment).** -/
theorem exists_orthonormal_sum_inner_eq_kyFanSum {T : H →L[ℂ] H} (hT : IsCompactOperator T) (N : ℕ) :
    ∃ r ≤ N, ∃ u v : Fin r → H, Orthonormal ℂ u ∧ Orthonormal ℂ v ∧
      ∑ k, ⟪v k, T (u k)⟫_ℂ = (kyFanSum T N : ℂ) := by
  classical
  set s := singVal T
  set r := Nat.findGreatest (fun r => ∀ j < r, s j ≠ 0) N with hr_def
  have hrN : r ≤ N := Nat.findGreatest_le N
  have hpos : ∀ j < r, s j ≠ 0 := by
    intro j hj
    exact Nat.findGreatest_spec (P := fun r => ∀ j < r, s j ≠ 0) (m := 0) (Nat.zero_le N)
      (fun j hj => absurd hj (Nat.not_lt_zero j)) j hj
  have hzero : ∀ j, r ≤ j → j < N → s j = 0 := by
    intro j hrj hjN
    by_contra hne
    have hsr : s r ≠ 0 := by
      intro h0
      exact hne (le_antisymm (h0 ▸ singVal_antitone T hrj) (singVal_nonneg T j))
    have hP : ∀ i < r + 1, s i ≠ 0 := fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | h1
      · exact hpos i h1
      · rw [h1]; exact hsr
    exact Nat.findGreatest_is_greatest (P := fun r => ∀ j < r, s j ≠ 0) (Nat.lt_succ_self r)
      (by omega) hP
  refine ⟨r, hrN, fun k => svVec (energyOp T) k, fun k => leftSingularVec T k, ?_, ?_, ?_⟩
  · refine ⟨fun k => norm_svVec_energyOp_of_singVal_ne_zero hT (hpos k k.2), fun i j hij => ?_⟩
    exact inner_svVec_energyOp_orthogonal fun h => hij (Fin.ext h)
  · refine ⟨fun k => ?_, fun i j hij => leftSingularVec_orthogonal fun h => hij (Fin.ext h)⟩
    rcases leftSingularVec_eq_zero_or_norm_eq_one hT k with h0 | h1
    · exfalso
      have := apply_svVec_eq_smul_leftSingularVec (T := T) k
      rw [h0, smul_zero] at this
      have hn := norm_apply_svVec_energyOp (T := T) k
      rw [this, norm_zero, norm_svVec_energyOp_of_singVal_ne_zero hT (hpos k k.2), mul_one] at hn
      exact hpos k k.2 hn.symm
    · exact h1
  · have hterm : ∀ k : Fin r, ⟪leftSingularVec T k, T (svVec (energyOp T) k)⟫_ℂ = (s k : ℂ) := by
      intro k
      rw [apply_svVec_eq_smul_leftSingularVec, inner_smul_right, inner_self_eq_norm_sq_to_K]
      rcases leftSingularVec_eq_zero_or_norm_eq_one hT k with h0 | h1
      · exfalso
        have := apply_svVec_eq_smul_leftSingularVec (T := T) k
        rw [h0, smul_zero] at this
        have hn := norm_apply_svVec_energyOp (T := T) k
        rw [this, norm_zero, norm_svVec_energyOp_of_singVal_ne_zero hT (hpos k k.2), mul_one] at hn
        exact hpos k k.2 hn.symm
      · rw [h1]; simp [s]
    rw [Finset.sum_congr rfl fun k _ => hterm k, kyFanSum]
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun k => (s k : ℂ)) r]
    have hsplit : ∑ j ∈ range N, ((approxNumber T j : ℝ) : ℂ) = ∑ j ∈ range r, (s j : ℂ) := by
      rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le r) hrN, ← range_eq_Ico]
      rw [sum_eq_zero (s := Ico r N) fun j hj => by
        have h0 := hzero j (mem_Ico.1 hj).1 (mem_Ico.1 hj).2
        simp only [s] at h0
        rw [approxNumber_eq_singVal hT j, h0]; simp, add_zero]
      exact sum_congr rfl fun j _ => by rw [approxNumber_eq_singVal hT j]
    exact hsplit.symm

/-- **Ky Fan's inequality** `K_N(A + B) ≤ K_N(A) + K_N(B)`. -/
theorem kyFanSum_add_le {A B : H →L[ℂ] H} (hA : IsCompactOperator A) (hB : IsCompactOperator B)
    (N : ℕ) : kyFanSum (A + B) N ≤ kyFanSum A N + kyFanSum B N := by
  have hAB : IsCompactOperator (A + B) := hA.add hB
  obtain ⟨r, hr, u, v, hu, hv, heq⟩ := exists_orthonormal_sum_inner_eq_kyFanSum hAB N
  have h1 := sum_norm_inner_le_kyFanSum hA hr hu hv
  have h2 := sum_norm_inner_le_kyFanSum hB hr hu hv
  have hre : kyFanSum (A + B) N = (∑ k, ⟪v k, (A + B) (u k)⟫_ℂ).re := by rw [heq]; simp
  rw [hre]
  simp only [add_apply, inner_add_right, sum_add_distrib, Complex.add_re]
  have hA' : (∑ k, ⟪v k, A (u k)⟫_ℂ).re ≤ ∑ k, ‖⟪v k, A (u k)⟫_ℂ‖ :=
    (Complex.re_le_norm _).trans (norm_sum_le _ _)
  have hB' : (∑ k, ⟪v k, B (u k)⟫_ℂ).re ≤ ∑ k, ‖⟪v k, B (u k)⟫_ℂ‖ :=
    (Complex.re_le_norm _).trans (norm_sum_le _ _)
  linarith

/-! ## Weyl's inequality -/

section Weyl

open Module Submodule

variable (T : H →L[ℂ] H)

/-- The generalized eigenspace `G(T, μ)`. -/
abbrev genEigen (μ : ℂ) : Submodule ℂ H :=
  Module.End.maxGenEigenspace ((T : H →ₗ[ℂ] H) : Module.End ℂ H) μ

omit [CompleteSpace H] in
theorem sub_smul_apply_end (ν : ℂ) (x : H) :
    (((T : H →ₗ[ℂ] H) : Module.End ℂ H) - ν • 1) x = T x - ν • x := by
  simp

omit [CompleteSpace H] in
/-- One step of the Schur flag: a unit vector `x ⊥ W` in `W ⊔ G(T, ν)` with `(T − ν)x ∈ W`. -/
theorem exists_unit_flag_step {W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hW : ∀ w ∈ W, T w ∈ W) {ν : ℂ} {y : H} (hy : y ∈ genEigen T ν) (hyW : y ∉ W) :
    ∃ x : H, ‖x‖ = 1 ∧ x ∈ Wᗮ ∧ x ∈ W ⊔ genEigen T ν ∧ T x - ν • x ∈ W := by
  classical
  set N : Module.End ℂ H := ((T : H →ₗ[ℂ] H) : Module.End ℂ H) - ν • 1 with hN
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hy
  set P : ℕ → Prop := fun j => (N ^ j) y ∉ W
  have hP0 : P 0 := by simpa [P] using hyW
  set j := Nat.findGreatest P k with hj_def
  have hPj : P j := Nat.findGreatest_spec (P := P) (Nat.zero_le k) hP0
  have hjk : j < k := by
    rcases (Nat.findGreatest_le (P := P) k).lt_or_eq with h | h
    · exact h
    · exfalso; apply hPj; rw [hj_def, h]; simp [hN, hk]
  have hPj1 : ¬ P (j + 1) := Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self j) hjk
  set z := (N ^ j) y with hz_def
  have hzW : z ∉ W := hPj
  have hNz : N z ∈ W := by
    have h := not_not.1 hPj1
    rwa [pow_succ', Module.End.mul_apply] at h
  have hzG : z ∈ genEigen T ν := by
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
    rw [hz_def, ← Module.End.mul_apply, ← pow_add, add_comm, pow_add, Module.End.mul_apply, hk, map_zero]
  have hNW : ∀ v ∈ W, N v ∈ W := fun v hv => by
    rw [hN, sub_smul_apply_end]; exact W.sub_mem (hW v hv) (W.smul_mem ν hv)
  set w := z - W.starProjection z with hw_def
  have hw0 : w ≠ 0 := fun h => hzW (by
    rw [hw_def, sub_eq_zero] at h; rw [h]; exact W.starProjection_apply_mem z)
  have hwW : w ∈ Wᗮ := W.sub_starProjection_mem_orthogonal z
  have hNw : N w ∈ W := by
    rw [hw_def, map_sub]; exact W.sub_mem hNz (hNW _ (W.starProjection_apply_mem z))
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  refine ⟨((‖w‖⁻¹ : ℝ) : ℂ) • w, ?_, Wᗮ.smul_mem _ hwW, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hwpos),
      inv_mul_cancel₀ hwpos.ne']
  · refine (W ⊔ genEigen T ν).smul_mem _ ?_
    exact (W ⊔ genEigen T ν).sub_mem (mem_sup_right hzG) (mem_sup_left (W.starProjection_apply_mem z))
  · have h : T (((‖w‖⁻¹ : ℝ) : ℂ) • w) - ν • (((‖w‖⁻¹ : ℝ) : ℂ) • w) =
        ((‖w‖⁻¹ : ℝ) : ℂ) • N w := by
      rw [hN, sub_smul_apply_end, map_smul]
      module
    rw [h]; exact W.smul_mem _ hNw

omit [CompleteSpace H] in
theorem orthonormal_snoc {n : ℕ} {u : Fin n → H} (hu : Orthonormal ℂ u) {x : H} (hx : ‖x‖ = 1)
    (hxu : ∀ i, ⟪u i, x⟫_ℂ = 0) : Orthonormal ℂ (Fin.snoc (α := fun _ => H) u x) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hx
    · simpa using hu.1 i
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j => simp only [Fin.snoc_last, Fin.snoc_castSucc]; rw [← inner_conj_symm, hxu j, map_zero]
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hxu i
      | cast j =>
        simp only [Fin.snoc_castSucc]
        exact hu.2 fun h => hij (by rw [h])

omit [CompleteSpace H] in
/-- A block of the Schur flag: `t ≤ dim G(T, ν)` new orthonormal vectors with diagonal entry `ν`. -/
theorem exists_orthonormal_flag_block {n : ℕ} {u : Fin n → H} (hu : Orthonormal ℂ u)
    (hW : ∀ w ∈ span ℂ (Set.range u), T w ∈ span ℂ (Set.range u)) {V : Submodule ℂ H}
    (hWV : span ℂ (Set.range u) ≤ V) {ν : ℂ} [FiniteDimensional ℂ (genEigen T ν)]
    (hdisj : Disjoint V (genEigen T ν)) :
    ∀ t ≤ finrank ℂ (genEigen T ν), ∃ u' : Fin (n + t) → H, Orthonormal ℂ u' ∧
      (∀ i : Fin n, u' (Fin.castAdd t i) = u i) ∧
      (∀ i : Fin t, ⟪u' (Fin.natAdd n i), T (u' (Fin.natAdd n i))⟫_ℂ = ν) ∧
      (∀ w ∈ span ℂ (Set.range u'), T w ∈ span ℂ (Set.range u')) ∧
      span ℂ (Set.range u') ≤ V ⊔ genEigen T ν := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨u, hu, fun i => rfl, fun i => i.elim0, hW, hWV.trans le_sup_left⟩
  | succ t ih =>
    intro ht
    obtain ⟨u', hu', hext, hdiag, hinv, hle⟩ := ih (Nat.le_of_succ_le ht)
    set W' := span ℂ (Set.range u')
    haveI : FiniteDimensional ℂ W' := FiniteDimensional.span_of_finite ℂ (Set.finite_range u')
    haveI : FiniteDimensional ℂ (span ℂ (Set.range u)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
    have hfinW' : finrank ℂ W' = n + t := by
      rw [finrank_span_eq_card hu'.linearIndependent, Fintype.card_fin]
    have hWW' : span ℂ (Set.range u) ≤ W' := span_le.2 fun _ ⟨i, hi⟩ => by
      rw [← hi, ← hext i]; exact subset_span ⟨_, rfl⟩
    have hnot : ¬ genEigen T ν ≤ W' := by
      intro hG
      have hsup : span ℂ (Set.range u) ⊔ genEigen T ν ≤ W' := sup_le hWW' hG
      have hinf : span ℂ (Set.range u) ⊓ genEigen T ν = ⊥ :=
        disjoint_iff.1 (hdisj.mono_left hWV)
      have hrank := Submodule.finrank_sup_add_finrank_inf_eq (span ℂ (Set.range u)) (genEigen T ν)
      rw [hinf, finrank_bot, add_zero, finrank_span_eq_card hu.linearIndependent, Fintype.card_fin]
        at hrank
      have := Submodule.finrank_mono hsup
      omega
    obtain ⟨y, hyG, hyW⟩ := SetLike.not_le_iff_exists.1 hnot
    obtain ⟨x, hx1, hxW, hxsup, hTx⟩ := exists_unit_flag_step T hinv hyG hyW
    have hxu : ∀ i, ⟪u' i, x⟫_ℂ = 0 := fun i =>
      (mem_orthogonal' W' x).1 hxW (u' i) (subset_span ⟨i, rfl⟩) |> fun h => by
        rw [← inner_conj_symm, h, map_zero]
    refine ⟨Fin.snoc (α := fun _ => H) u' x, orthonormal_snoc hu' hx1 hxu, fun i => ?_, fun i => ?_,
      ?_, ?_⟩
    · show Fin.snoc (α := fun _ => H) u' x (Fin.castSucc (Fin.castAdd t i)) = u i
      rw [Fin.snoc_castSucc, hext]
    · induction i using Fin.lastCases with
      | last =>
        show ⟪Fin.snoc (α := fun _ => H) u' x (Fin.last (n + t)),
          T (Fin.snoc (α := fun _ => H) u' x (Fin.last (n + t)))⟫_ℂ = ν
        rw [Fin.snoc_last]
        have hdec : T x = ν • x + (T x - ν • x) := by abel
        rw [hdec, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx1,
          (mem_orthogonal' W' x).1 hxW _ hTx]
        simp
      | cast i =>
        show ⟪Fin.snoc (α := fun _ => H) u' x (Fin.castSucc (Fin.natAdd n i)),
          T (Fin.snoc (α := fun _ => H) u' x (Fin.castSucc (Fin.natAdd n i)))⟫_ℂ = ν
        rw [Fin.snoc_castSucc]; exact hdiag i
    · have hgen : ∀ i, T (Fin.snoc (α := fun _ => H) u' x i) ∈
          span ℂ (Set.range (Fin.snoc (α := fun _ => H) u' x)) := by
        have hW'sub : W' ≤ span ℂ (Set.range (Fin.snoc (α := fun _ => H) u' x)) :=
          span_le.2 fun _ ⟨i, hi⟩ => by
            rw [← hi]; exact subset_span ⟨Fin.castSucc i, Fin.snoc_castSucc (α := fun _ => H) _ _ _⟩
        intro i
        induction i using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last]
          have hdec : T x = ν • x + (T x - ν • x) := by abel
          rw [hdec]
          refine add_mem (smul_mem _ _ (subset_span ⟨Fin.last _, Fin.snoc_last (α := fun _ => H) _ _⟩))
            (hW'sub hTx)
        | cast i =>
          rw [Fin.snoc_castSucc]; exact hW'sub (hinv _ (subset_span ⟨i, rfl⟩))
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw => obtain ⟨i, rfl⟩ := hw; exact hgen i
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha => rw [map_smul]; exact smul_mem _ _ ha
    · refine span_le.2 fun _ ⟨i, hi⟩ => ?_
      rw [← hi]
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact sup_le hle le_sup_right hxsup
      | cast i => rw [Fin.snoc_castSucc]; exact hle (subset_span ⟨i, rfl⟩)

omit [CompleteSpace H] in
/-- The complete Schur flag for finitely many distinct eigenvalues with prescribed multiplicities. -/
theorem exists_orthonormal_weyl_flag (s : Finset ℂ) (m : ℂ → ℕ)
    (hfin : ∀ μ ∈ s, FiniteDimensional ℂ (genEigen T μ))
    (hm : ∀ μ ∈ s, m μ ≤ finrank ℂ (genEigen T μ)) :
    ∃ u : Fin (∑ μ ∈ s, m μ) → H, Orthonormal ℂ u ∧
      ∑ k, ‖⟪u k, T (u k)⟫_ℂ‖ = ∑ μ ∈ s, m μ * ‖μ‖ ∧
      (∀ w ∈ span ℂ (Set.range u), T w ∈ span ℂ (Set.range u)) ∧
      span ℂ (Set.range u) ≤ ⨆ μ ∈ s, genEigen T μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, by simp, fun w hw => ?_, by simp⟩
    rw [Set.range_eq_empty, span_empty, Submodule.mem_bot] at hw
    rw [hw, map_zero]; exact zero_mem _
  | insert ν s hν ih =>
    obtain ⟨u, hu, hsum, hinv, hle⟩ := ih (fun μ hμ => hfin μ (mem_insert_of_mem hμ))
      (fun μ hμ => hm μ (mem_insert_of_mem hμ))
    haveI := hfin ν (mem_insert_self ν s)
    have hdisj : Disjoint (⨆ μ ∈ s, genEigen T μ) (genEigen T ν) :=
      ((Module.End.independent_maxGenEigenspace _).disjoint_biSup (y := (s : Set ℂ))
        (by simpa using hν)).symm
    obtain ⟨u', hu', hext, hdiag, hinv', hle'⟩ :=
      exists_orthonormal_flag_block T hu hinv hle hdisj (m ν) (hm ν (mem_insert_self ν s))
    have hcard : (∑ μ ∈ s, m μ) + m ν = ∑ μ ∈ insert ν s, m μ := by
      rw [sum_insert hν, add_comm]
    refine ⟨u' ∘ Fin.cast hcard.symm, hu'.comp _ (Fin.cast_injective _), ?_, ?_, ?_⟩
    · conv_rhs => rw [sum_insert hν]
      have hre : ∑ k, ‖⟪(u' ∘ Fin.cast hcard.symm) k, T ((u' ∘ Fin.cast hcard.symm) k)⟫_ℂ‖ =
          ∑ k, ‖⟪u' k, T (u' k)⟫_ℂ‖ :=
        Fintype.sum_equiv (finCongr hcard.symm) _ _ fun k => rfl
      rw [hre, Fin.sum_univ_add]
      have h1 : ∑ i : Fin (∑ μ ∈ s, m μ), ‖⟪u' (Fin.castAdd (m ν) i), T (u' (Fin.castAdd (m ν) i))⟫_ℂ‖ =
          ∑ μ ∈ s, m μ * ‖μ‖ := by
        rw [← hsum]; exact sum_congr rfl fun i _ => by rw [hext]
      have h2 : ∑ i : Fin (m ν), ‖⟪u' (Fin.natAdd _ i), T (u' (Fin.natAdd _ i))⟫_ℂ‖ = m ν * ‖ν‖ := by
        simp_rw [hdiag]; simp
      rw [h1, h2]; ring
    · have hrange : Set.range (u' ∘ Fin.cast hcard.symm) = Set.range u' :=
        (finCongr hcard.symm).surjective.range_comp u'
      rw [hrange]; exact hinv'
    · have hrange : Set.range (u' ∘ Fin.cast hcard.symm) = Set.range u' :=
        (finCongr hcard.symm).surjective.range_comp u'
      rw [hrange]
      refine hle'.trans (sup_le ?_ ?_)
      · exact biSup_mono fun μ hμ => mem_insert_of_mem hμ
      · exact le_biSup (fun μ => genEigen T μ) (mem_insert_self ν s)

/-- **Weyl's inequality** `Σ_i m_i |μ_i| ≤ K_{Σ m_i}(T)`. -/
theorem sum_mul_norm_le_kyFanSum {T : H →L[ℂ] H} (hT : IsCompactOperator T) (s : Finset ℂ) (m : ℂ → ℕ)
    (hfin : ∀ μ ∈ s, FiniteDimensional ℂ (genEigen T μ))
    (hm : ∀ μ ∈ s, m μ ≤ finrank ℂ (genEigen T μ)) :
    ∑ μ ∈ s, m μ * ‖μ‖ ≤ kyFanSum T (∑ μ ∈ s, m μ) := by
  obtain ⟨u, hu, hsum, -, -⟩ := exists_orthonormal_weyl_flag T s m hfin hm
  rw [← hsum]
  exact sum_norm_inner_le_kyFanSum hT le_rfl hu hu

end Weyl

end

end GaloisForLFunctions.HTGeometry
