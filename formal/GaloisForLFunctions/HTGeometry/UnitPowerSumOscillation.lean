import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Unit power sums oscillate below every decaying floor

For a nonempty finite family of unit-modulus complex numbers, none equal to `1`, the real parts
of the power sums `A n = sum_i v_i ^ (n+1)` cannot stay above `-(C k^n)` with `0 ≤ k < 1`.

The proof is a finite second-moment argument.  Cesàro sums of `z^(n+1)` are bounded by
`2/‖z-1‖` for unit `z ≠ 1`, so the partial sums of `Re (A n)` stay bounded, while the identity
`(Re A)^2 = (‖A‖^2 + Re (A^2))/2` and the expansion of `‖A n‖^2` over pairs — whose diagonal
contributes `+N` per index — force `sum_(n<N) (Re A_n)^2` to grow linearly in `N`.  A decaying
lower floor makes `|Re A_n|` summably close to `Re A_n`, so the square sum is also bounded — a
contradiction.  Everything is effective: the implied threshold is explicit in the data.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Geometric sum bound on the closed unit disc. -/
theorem norm_geom_sum_le_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  have h1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr h1
  rw [geom_sum_eq hz1, norm_div]
  rw [div_le_div_iff₀ hpos hpos]
  have hnum : ‖z ^ N - 1‖ ≤ 2 := by
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          rw [norm_pow, norm_one]
          exact add_le_add (pow_le_one₀ (norm_nonneg z) hz) le_rfl
      _ = 2 := by norm_num
  exact mul_le_mul_of_nonneg_right hnum hpos.le

/-- Shifted geometric sum bound. -/
theorem norm_sum_pow_succ_le {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ (n + 1)‖ ≤ 2 / ‖z - 1‖ := by
  have h : ∑ n ∈ Finset.range N, z ^ (n + 1) = z * ∑ n ∈ Finset.range N, z ^ n := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [pow_succ']
  rw [h, norm_mul]
  calc ‖z‖ * ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 1 * (2 / ‖z - 1‖) :=
        mul_le_mul hz (norm_geom_sum_le_of_norm_le_one hz hz1 N) (norm_nonneg _) zero_le_one
    _ = 2 / ‖z - 1‖ := one_mul _

/-- Real-part floor for unit power sums: `0` when `z = 1` (the sum is `N`), otherwise
`-2/‖z-1‖`. -/
theorem re_sum_pow_succ_ge {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    (if z = 1 then (0 : ℝ) else -(2 / ‖z - 1‖)) ≤
      (∑ n ∈ Finset.range N, z ^ (n + 1)).re := by
  by_cases h1 : z = 1
  · rw [if_pos h1]
    simp [h1]
  · rw [if_neg h1]
    have hb := norm_sum_pow_succ_le (le_of_eq hz) h1 N
    have h2 := Complex.abs_re_le_norm (∑ n ∈ Finset.range N, z ^ (n + 1))
    have h3 := neg_abs_le (∑ n ∈ Finset.range N, z ^ (n + 1)).re
    linarith

/-- **Unit power sums oscillate.**  A nonempty finite family of unit-modulus points, none equal
to `1`, cannot have all real power sums `Re (sum_i v_i^(n+1))` above a decaying floor
`-(C k^n)`, `0 ≤ k < 1`. -/
theorem unitPowerSum_no_decaying_lower_bound {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {v : ι → ℂ} (hnorm : ∀ i ∈ s, ‖v i‖ = 1)
    (hne : ∀ i ∈ s, v i ≠ 1) {C κ : ℝ} (hC : 0 ≤ C) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hlow : ∀ n : ℕ, -(C * κ ^ n) ≤ (∑ i ∈ s, v i ^ (n + 1)).re) : False := by
  classical
  set K : ℝ := (s.card : ℝ) with hK
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hK]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  set A : ℕ → ℂ := fun n => ∑ i ∈ s, v i ^ (n + 1) with hA
  have hAbound : ∀ n, ‖A n‖ ≤ K := by
    intro n
    calc ‖A n‖ ≤ ∑ i ∈ s, ‖v i ^ (n + 1)‖ := norm_sum_le _ _
      _ = ∑ _i ∈ s, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [norm_pow, hnorm i hi, one_pow]
      _ = K := by rw [Finset.sum_const, hK, nsmul_eq_mul, mul_one]
  set C₁ : ℝ := ∑ i ∈ s, 2 / ‖v i - 1‖ with hC₁
  have hC₁nn : 0 ≤ C₁ := Finset.sum_nonneg fun i _ => by positivity
  set B : ι → ι → ℝ := fun i j =>
    if v i * (starRingEnd ℂ) (v j) = 1 then 0 else 2 / ‖v i * (starRingEnd ℂ) (v j) - 1‖
    with hB
  set B' : ι → ι → ℝ := fun i j =>
    if v i * v j = 1 then 0 else 2 / ‖v i * v j - 1‖ with hB'
  have hBnn : ∀ i j, 0 ≤ B i j := by
    intro i j
    simp only [hB]
    split <;> positivity
  have hB'nn : ∀ i j, 0 ≤ B' i j := by
    intro i j
    simp only [hB']
    split <;> positivity
  set C₄ : ℝ := ∑ i ∈ s, ∑ j ∈ s, B i j with hC₄
  set C₅ : ℝ := ∑ i ∈ s, ∑ j ∈ s, B' i j with hC₅
  -- (1) bounded partial sums of A
  have hsum1 : ∀ N, ‖∑ n ∈ Finset.range N, A n‖ ≤ C₁ := by
    intro N
    have hswap : ∑ n ∈ Finset.range N, A n =
        ∑ i ∈ s, ∑ n ∈ Finset.range N, v i ^ (n + 1) := by
      rw [hA]
      exact Finset.sum_comm
    rw [hswap]
    calc ‖∑ i ∈ s, ∑ n ∈ Finset.range N, v i ^ (n + 1)‖
        ≤ ∑ i ∈ s, ‖∑ n ∈ Finset.range N, v i ^ (n + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, 2 / ‖v i - 1‖ :=
          Finset.sum_le_sum fun i hi =>
            norm_sum_pow_succ_le (le_of_eq (hnorm i hi)) (hne i hi) N
      _ = C₁ := hC₁.symm
  -- (2) linear growth of the norm-square sums
  have hunit : ∀ i ∈ s, ∀ j ∈ s, ‖v i * (starRingEnd ℂ) (v j)‖ = 1 := by
    intro i hi j hj
    rw [norm_mul, hnorm i hi, RCLike.norm_conj, hnorm j hj, one_mul]
  have hunit' : ∀ i ∈ s, ∀ j ∈ s, ‖v i * v j‖ = 1 := by
    intro i hi j hj
    rw [norm_mul, hnorm i hi, hnorm j hj, one_mul]
  have hdiag : ∀ i ∈ s, v i * (starRingEnd ℂ) (v i) = 1 := by
    intro i hi
    rw [Complex.mul_conj]
    rw [show Complex.normSq (v i) = 1 by
      rw [← Complex.sq_norm, hnorm i hi, one_pow]]
    norm_num
  have hsum2 : ∀ N : ℕ, K * N - C₄ ≤ ∑ n ∈ Finset.range N, ‖A n‖ ^ 2 := by
    intro N
    have hAsq : ∀ n, (‖A n‖ : ℝ) ^ 2 = (A n * (starRingEnd ℂ) (A n)).re := by
      intro n
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    have hexp : ∑ n ∈ Finset.range N, A n * (starRingEnd ℂ) (A n) =
        ∑ i ∈ s, ∑ j ∈ s,
          ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) := by
      have h1 : ∀ n, A n * (starRingEnd ℂ) (A n) =
          ∑ i ∈ s, ∑ j ∈ s, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) := by
        intro n
        rw [hA]
        simp only [map_sum]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [map_pow, mul_pow]
      calc ∑ n ∈ Finset.range N, A n * (starRingEnd ℂ) (A n)
          = ∑ n ∈ Finset.range N, ∑ i ∈ s, ∑ j ∈ s,
              (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) :=
            Finset.sum_congr rfl fun n _ => h1 n
        _ = ∑ i ∈ s, ∑ n ∈ Finset.range N, ∑ j ∈ s,
              (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) := Finset.sum_comm
        _ = ∑ i ∈ s, ∑ j ∈ s,
              ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
    have hre : ∑ n ∈ Finset.range N, ‖A n‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s,
          (∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
      calc ∑ n ∈ Finset.range N, ‖A n‖ ^ 2
          = ∑ n ∈ Finset.range N, (A n * (starRingEnd ℂ) (A n)).re :=
            Finset.sum_congr rfl fun n _ => hAsq n
        _ = (∑ n ∈ Finset.range N, A n * (starRingEnd ℂ) (A n)).re :=
            (Complex.re_sum _ _).symm
        _ = ∑ i ∈ s, ∑ j ∈ s,
              (∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
            rw [hexp, Complex.re_sum]
            exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
    rw [hre]
    have hper : ∀ i ∈ s, (N : ℝ) - ∑ j ∈ s, B i j ≤
        ∑ j ∈ s, (∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
      intro i hi
      rw [← Finset.add_sum_erase s
        (fun j => (∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re) hi]
      have hdiagval : (∑ n ∈ Finset.range N,
          (v i * (starRingEnd ℂ) (v i)) ^ (n + 1)).re = (N : ℝ) := by
        rw [hdiag i hi]
        simp
      rw [hdiagval]
      have hrest : -∑ j ∈ s, B i j ≤
          ∑ j ∈ s.erase i, (∑ n ∈ Finset.range N,
            (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
        have hstep : ∀ j ∈ s.erase i, -(B i j) ≤
            (∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
          intro j hj
          have hjs := Finset.mem_of_mem_erase hj
          have h := re_sum_pow_succ_ge (hunit i hi j hjs) N
          simp only [hB]
          split_ifs at h ⊢ with hcase
          · simpa using h
          · exact h
        calc -∑ j ∈ s, B i j ≤ -∑ j ∈ s.erase i, B i j := by
              have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i s)
                (fun j _ _ => hBnn i j)
              linarith
          _ ≤ ∑ j ∈ s.erase i, (∑ n ∈ Finset.range N,
                (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
              rw [neg_le]
              rw [← Finset.sum_neg_distrib]
              exact Finset.sum_le_sum fun j hj => by
                have := hstep j hj
                linarith

      linarith
    calc K * N - C₄ = ∑ _i ∈ s, (N : ℝ) - ∑ i ∈ s, ∑ j ∈ s, B i j := by
          rw [Finset.sum_const, hC₄, hK, nsmul_eq_mul]
      _ = ∑ i ∈ s, ((N : ℝ) - ∑ j ∈ s, B i j) := by
          rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ s, ∑ j ∈ s,
            (∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re :=
          Finset.sum_le_sum hper
  -- (3) bounded square sums
  have hsum3 : ∀ N : ℕ, -C₅ ≤ ∑ n ∈ Finset.range N, ((A n) ^ 2).re := by
    intro N
    have hexp : ∑ n ∈ Finset.range N, (A n) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1) := by
      have h1 : ∀ n, (A n) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (v i * v j) ^ (n + 1) := by
        intro n
        rw [hA, pow_two, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow]
      calc ∑ n ∈ Finset.range N, (A n) ^ 2
          = ∑ n ∈ Finset.range N, ∑ i ∈ s, ∑ j ∈ s, (v i * v j) ^ (n + 1) :=
            Finset.sum_congr rfl fun n _ => h1 n
        _ = ∑ i ∈ s, ∑ n ∈ Finset.range N, ∑ j ∈ s, (v i * v j) ^ (n + 1) :=
            Finset.sum_comm
        _ = ∑ i ∈ s, ∑ j ∈ s, ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
    have hre : ∑ n ∈ Finset.range N, ((A n) ^ 2).re =
        ∑ i ∈ s, ∑ j ∈ s, (∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re := by
      calc ∑ n ∈ Finset.range N, ((A n) ^ 2).re
          = (∑ n ∈ Finset.range N, (A n) ^ 2).re := (Complex.re_sum _ _).symm
        _ = ∑ i ∈ s, ∑ j ∈ s, (∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re := by
            rw [hexp, Complex.re_sum]
            exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
    rw [hre]
    have hstep : ∀ i ∈ s, ∀ j ∈ s, -(B' i j) ≤
        (∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re := by
      intro i hi j hj
      have h := re_sum_pow_succ_ge (hunit' i hi j hj) N
      simp only [hB']
      split_ifs at h ⊢ with hcase
      · simpa using h
      · exact h
    calc -C₅ = ∑ i ∈ s, ∑ j ∈ s, -(B' i j) := by
          rw [hC₅]
          simp [Finset.sum_neg_distrib]
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, (∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hstep i hi j hj
  -- (4) pointwise identity
  have hid : ∀ n, ((A n).re) ^ 2 = (‖A n‖ ^ 2 + ((A n) ^ 2).re) / 2 := by
    intro n
    rw [Complex.sq_norm, Complex.normSq_apply, pow_two (A n), Complex.mul_re]
    ring
  -- (5) upper bound for the square sums
  have h1κ : (0 : ℝ) < 1 - κ := by linarith
  have hup : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((A n).re) ^ 2 ≤
      K * (C₁ + 2 * C / (1 - κ)) := by
    intro N
    have habs : ∀ n, |(A n).re| ≤ (A n).re + 2 * C * κ ^ n := by
      intro n
      rcases abs_cases (A n).re with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
        nlinarith [mul_nonneg hC (pow_nonneg hκ0 n)]
      · rw [h]
        have := hlow n
        nlinarith
    have hgeo : ∑ n ∈ Finset.range N, κ ^ n ≤ 1 / (1 - κ) := by
      have hκne : κ ≠ 1 := ne_of_lt hκ1
      rw [geom_sum_eq hκne]
      rw [show κ ^ N - 1 = -(1 - κ ^ N) by ring, show κ - 1 = -(1 - κ) by ring,
        neg_div_neg_eq]
      rw [div_le_div_iff₀ h1κ h1κ]
      nlinarith [pow_nonneg hκ0 N]
    calc ∑ n ∈ Finset.range N, ((A n).re) ^ 2
        ≤ ∑ n ∈ Finset.range N, K * |(A n).re| := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h1 : |(A n).re| ≤ K := le_trans (Complex.abs_re_le_norm _) (hAbound n)
          nlinarith [abs_nonneg ((A n).re), sq_abs ((A n).re)]
      _ = K * ∑ n ∈ Finset.range N, |(A n).re| := (Finset.mul_sum _ _ _).symm
      _ ≤ K * (C₁ + 2 * C / (1 - κ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          calc ∑ n ∈ Finset.range N, |(A n).re|
              ≤ ∑ n ∈ Finset.range N, ((A n).re + 2 * C * κ ^ n) :=
                Finset.sum_le_sum fun n _ => habs n
            _ = (∑ n ∈ Finset.range N, A n).re +
                  2 * C * ∑ n ∈ Finset.range N, κ ^ n := by
                rw [Finset.sum_add_distrib, Complex.re_sum, ← Finset.mul_sum]
            _ ≤ C₁ + 2 * C / (1 - κ) := by
                have h1 : (∑ n ∈ Finset.range N, A n).re ≤ C₁ :=
                  le_trans (Complex.re_le_norm _) (hsum1 N)
                have h2 : 2 * C * ∑ n ∈ Finset.range N, κ ^ n ≤ 2 * C * (1 / (1 - κ)) :=
                  mul_le_mul_of_nonneg_left hgeo (by linarith)
                have h3 : 2 * C * (1 / (1 - κ)) = 2 * C / (1 - κ) := by ring
                linarith
  -- (6) lower bound for the square sums and the contradiction
  have hlowN : ∀ N : ℕ, (K * N - (C₄ + C₅)) / 2 ≤
      ∑ n ∈ Finset.range N, ((A n).re) ^ 2 := by
    intro N
    have h2 := hsum2 N
    have h3 := hsum3 N
    have hEq : (2 : ℝ) * ∑ n ∈ Finset.range N, ((A n).re) ^ 2 =
        (∑ n ∈ Finset.range N, ‖A n‖ ^ 2) +
          ∑ n ∈ Finset.range N, ((A n) ^ 2).re := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hid n]
      ring
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((K * (C₁ + 2 * C / (1 - κ)) * 2 + (C₄ + C₅)) / K)
  have hKpos : (0 : ℝ) < K := by linarith
  rw [div_lt_iff₀ hKpos] at hN
  have hfin1 := hlowN N
  have hfin2 := hup N
  nlinarith

end GaloisForLFunctions.HTGeometry

end
