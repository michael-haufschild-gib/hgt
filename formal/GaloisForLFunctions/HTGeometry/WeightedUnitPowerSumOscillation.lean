import GaloisForLFunctions.HTGeometry.UnitPowerSumOscillation

/-!
# Positive-weight unit power sums oscillate below every decaying floor

The unit-power-sum edge mechanism remains valid with arbitrary strictly positive real atom
weights.  This is essential for coefficient-faithful source carriers: flattening weights to a
support indicator is unnecessary.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A nonempty finite positive-weight family of unit-modulus points, none equal to `1`, cannot
have every weighted real power sum above a geometrically decaying negative floor. -/
theorem weightedUnitPowerSum_no_decaying_lower_bound
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {v : ι → ℂ} (hnorm : ∀ i ∈ s, ‖v i‖ = 1)
    (hne : ∀ i ∈ s, v i ≠ 1)
    {w : ι → ℝ} (hw : ∀ i ∈ s, 0 < w i)
    {C κ : ℝ} (hC : 0 ≤ C) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hlow : ∀ n : ℕ,
      -(C * κ ^ n) ≤ (∑ i ∈ s, (w i : ℂ) * v i ^ (n + 1)).re) : False := by
  classical
  set K₁ : ℝ := ∑ i ∈ s, w i with hK₁
  set K₂ : ℝ := ∑ i ∈ s, (w i) ^ 2 with hK₂
  obtain ⟨i₀, hi₀⟩ := hs
  have hK₁pos : 0 < K₁ :=
    Finset.sum_pos' (fun i hi => (hw i hi).le) ⟨i₀, hi₀, hw i₀ hi₀⟩
  have hK₂pos : 0 < K₂ :=
    Finset.sum_pos' (fun i _ => sq_nonneg (w i))
      ⟨i₀, hi₀, sq_pos_of_pos (hw i₀ hi₀)⟩
  set A : ℕ → ℂ := fun n =>
    ∑ i ∈ s, (w i : ℂ) * v i ^ (n + 1) with hA
  have hAbound : ∀ n, ‖A n‖ ≤ K₁ := by
    intro n
    calc
      ‖A n‖ ≤ ∑ i ∈ s, ‖(w i : ℂ) * v i ^ (n + 1)‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, w i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [norm_mul, norm_pow, hnorm i hi, one_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hw i hi)]
        ring
      _ = K₁ := hK₁.symm
  set C₁ : ℝ := ∑ i ∈ s, w i * (2 / ‖v i - 1‖) with hC₁
  have hC₁nn : 0 ≤ C₁ := Finset.sum_nonneg fun i hi =>
    mul_nonneg (hw i hi).le (by positivity)
  set B : ι → ι → ℝ := fun i j =>
    w i * w j *
      (if v i * (starRingEnd ℂ) (v j) = 1 then 0
        else 2 / ‖v i * (starRingEnd ℂ) (v j) - 1‖) with hB
  set B' : ι → ι → ℝ := fun i j =>
    w i * w j *
      (if v i * v j = 1 then 0 else 2 / ‖v i * v j - 1‖) with hB'
  have hBnn : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ B i j := by
    intro i hi j hj
    simp only [hB]
    exact mul_nonneg (mul_nonneg (hw i hi).le (hw j hj).le) (by split <;> positivity)
  have hB'nn : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ B' i j := by
    intro i hi j hj
    simp only [hB']
    exact mul_nonneg (mul_nonneg (hw i hi).le (hw j hj).le) (by split <;> positivity)
  set C₄ : ℝ := ∑ i ∈ s, ∑ j ∈ s, B i j with hC₄
  set C₅ : ℝ := ∑ i ∈ s, ∑ j ∈ s, B' i j with hC₅
  have hsum1 : ∀ N, ‖∑ n ∈ Finset.range N, A n‖ ≤ C₁ := by
    intro N
    have hswap : ∑ n ∈ Finset.range N, A n =
        ∑ i ∈ s, (w i : ℂ) * ∑ n ∈ Finset.range N, v i ^ (n + 1) := by
      rw [hA]
      calc
        ∑ n ∈ Finset.range N, ∑ i ∈ s, (w i : ℂ) * v i ^ (n + 1) =
            ∑ i ∈ s, ∑ n ∈ Finset.range N, (w i : ℂ) * v i ^ (n + 1) :=
              Finset.sum_comm
        _ = ∑ i ∈ s, (w i : ℂ) * ∑ n ∈ Finset.range N, v i ^ (n + 1) := by
              refine Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _ |>.symm
    rw [hswap]
    calc
      ‖∑ i ∈ s, (w i : ℂ) * ∑ n ∈ Finset.range N, v i ^ (n + 1)‖ ≤
          ∑ i ∈ s, ‖(w i : ℂ) * ∑ n ∈ Finset.range N, v i ^ (n + 1)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ i ∈ s, w i * (2 / ‖v i - 1‖) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw i hi)]
          exact mul_le_mul_of_nonneg_left
            (norm_sum_pow_succ_le (le_of_eq (hnorm i hi)) (hne i hi) N) (hw i hi).le
      _ = C₁ := hC₁.symm
  have hunit : ∀ i ∈ s, ∀ j ∈ s,
      ‖v i * (starRingEnd ℂ) (v j)‖ = 1 := by
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
  have hsum2 : ∀ N : ℕ,
      K₂ * N - C₄ ≤ ∑ n ∈ Finset.range N, ‖A n‖ ^ 2 := by
    intro N
    have hAsq : ∀ n, (‖A n‖ : ℝ) ^ 2 =
        (A n * (starRingEnd ℂ) (A n)).re := by
      intro n
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    have hexp : ∑ n ∈ Finset.range N, A n * (starRingEnd ℂ) (A n) =
        ∑ i ∈ s, ∑ j ∈ s, (w i * w j : ℂ) *
          ∑ n ∈ Finset.range N,
            (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) := by
      have h1 : ∀ n, A n * (starRingEnd ℂ) (A n) =
          ∑ i ∈ s, ∑ j ∈ s, (w i * w j : ℂ) *
            (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) := by
        intro n
        rw [hA]
        simp only [map_sum, map_mul, map_pow, Complex.conj_ofReal]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow]
        ring
      calc
        ∑ n ∈ Finset.range N, A n * (starRingEnd ℂ) (A n) =
            ∑ n ∈ Finset.range N, ∑ i ∈ s, ∑ j ∈ s,
              (w i * w j : ℂ) *
                (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) :=
                  Finset.sum_congr rfl fun n _ => h1 n
        _ = ∑ i ∈ s, ∑ j ∈ s, ∑ n ∈ Finset.range N,
              (w i * w j : ℂ) *
                (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) := by
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i ∈ s, ∑ j ∈ s, (w i * w j : ℂ) *
              ∑ n ∈ Finset.range N,
                (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) := by
                  refine Finset.sum_congr rfl fun i _ =>
                    Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _ |>.symm
    have hre : ∑ n ∈ Finset.range N, ‖A n‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s,
          ((w i * w j : ℂ) * ∑ n ∈ Finset.range N,
            (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
      calc
        ∑ n ∈ Finset.range N, ‖A n‖ ^ 2 =
            ∑ n ∈ Finset.range N, (A n * (starRingEnd ℂ) (A n)).re :=
              Finset.sum_congr rfl fun n _ => hAsq n
        _ = (∑ n ∈ Finset.range N, A n * (starRingEnd ℂ) (A n)).re :=
              (Complex.re_sum _ _).symm
        _ = _ := by
          rw [hexp, Complex.re_sum]
          exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
    rw [hre]
    have hper : ∀ i ∈ s,
        w i ^ 2 * N - ∑ j ∈ s, B i j ≤
          ∑ j ∈ s, ((w i * w j : ℂ) *
            ∑ n ∈ Finset.range N,
              (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
      intro i hi
      rw [← Finset.add_sum_erase s (fun j => ((w i * w j : ℂ) *
        ∑ n ∈ Finset.range N,
          (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re) hi]
      have hdiagval : ((w i * w i : ℂ) *
          ∑ n ∈ Finset.range N,
            (v i * (starRingEnd ℂ) (v i)) ^ (n + 1)).re = w i ^ 2 * N := by
        rw [hdiag i hi]
        simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Finset.card_range]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
        ring
      rw [hdiagval]
      have hrest : -∑ j ∈ s, B i j ≤
          ∑ j ∈ s.erase i, ((w i * w j : ℂ) *
            ∑ n ∈ Finset.range N,
              (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
        have hstep : ∀ j ∈ s.erase i, -(B i j) ≤
            ((w i * w j : ℂ) * ∑ n ∈ Finset.range N,
              (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
          intro j hj
          have hjs := Finset.mem_of_mem_erase hj
          have hbase := re_sum_pow_succ_ge (hunit i hi j hjs) N
          have hwij : 0 ≤ w i * w j := mul_nonneg (hw i hi).le (hw j hjs).le
          simp only [hB]
          split_ifs at hbase ⊢ with hcase
          · simpa [hcase, Complex.mul_re] using
              mul_nonneg hwij (Nat.cast_nonneg N)
          · have hmul := mul_le_mul_of_nonneg_left hbase hwij
            simpa [Complex.mul_re] using hmul
        calc
          -∑ j ∈ s, B i j ≤ -∑ j ∈ s.erase i, B i j := by
            have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i s)
              (fun j hj _ => hBnn i hi j hj)
            linarith
          _ ≤ ∑ j ∈ s.erase i, ((w i * w j : ℂ) *
              ∑ n ∈ Finset.range N,
                (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
            rw [neg_le, ← Finset.sum_neg_distrib]
            exact Finset.sum_le_sum fun j hj => by linarith [hstep j hj]
      linarith
    calc
      K₂ * N - C₄ = ∑ i ∈ s, (w i ^ 2 * N) -
          ∑ i ∈ s, ∑ j ∈ s, B i j := by
            rw [hK₂, hC₄, Finset.sum_mul]
      _ = ∑ i ∈ s, (w i ^ 2 * N - ∑ j ∈ s, B i j) := by
            rw [Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum hper
  have hsum3 : ∀ N : ℕ,
      -C₅ ≤ ∑ n ∈ Finset.range N, ((A n) ^ 2).re := by
    intro N
    have hexp : ∑ n ∈ Finset.range N, (A n) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, (w i * w j : ℂ) *
          ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1) := by
      have h1 : ∀ n, (A n) ^ 2 =
          ∑ i ∈ s, ∑ j ∈ s, (w i * w j : ℂ) *
            (v i * v j) ^ (n + 1) := by
        intro n
        rw [hA, pow_two, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow]
        ring
      calc
        ∑ n ∈ Finset.range N, (A n) ^ 2 =
            ∑ n ∈ Finset.range N, ∑ i ∈ s, ∑ j ∈ s,
              (w i * w j : ℂ) * (v i * v j) ^ (n + 1) :=
                Finset.sum_congr rfl fun n _ => h1 n
        _ = ∑ i ∈ s, ∑ j ∈ s, ∑ n ∈ Finset.range N,
              (w i * w j : ℂ) * (v i * v j) ^ (n + 1) := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = _ := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _ |>.symm
    have hre : ∑ n ∈ Finset.range N, ((A n) ^ 2).re =
        ∑ i ∈ s, ∑ j ∈ s, ((w i * w j : ℂ) *
          ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re := by
      calc
        ∑ n ∈ Finset.range N, ((A n) ^ 2).re =
            (∑ n ∈ Finset.range N, (A n) ^ 2).re := (Complex.re_sum _ _).symm
        _ = _ := by
          rw [hexp, Complex.re_sum]
          exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
    rw [hre]
    have hstep : ∀ i ∈ s, ∀ j ∈ s, -(B' i j) ≤
        ((w i * w j : ℂ) *
          ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re := by
      intro i hi j hj
      have hbase := re_sum_pow_succ_ge (hunit' i hi j hj) N
      have hwij : 0 ≤ w i * w j := mul_nonneg (hw i hi).le (hw j hj).le
      simp only [hB']
      split_ifs at hbase ⊢ with hcase
      · simpa [hcase, Complex.mul_re] using
          mul_nonneg hwij (Nat.cast_nonneg N)
      · have hmul := mul_le_mul_of_nonneg_left hbase hwij
        simpa [Complex.mul_re] using hmul
    calc
      -C₅ = ∑ i ∈ s, ∑ j ∈ s, -(B' i j) := by
        rw [hC₅]
        simp [Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        Finset.sum_le_sum fun j hj => hstep i hi j hj
  have hid : ∀ n,
      ((A n).re) ^ 2 = (‖A n‖ ^ 2 + ((A n) ^ 2).re) / 2 := by
    intro n
    rw [Complex.sq_norm, Complex.normSq_apply, pow_two (A n), Complex.mul_re]
    ring
  have h1κ : (0 : ℝ) < 1 - κ := by linarith
  have hup : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((A n).re) ^ 2 ≤
      K₁ * (C₁ + 2 * C / (1 - κ)) := by
    intro N
    have habs : ∀ n, |(A n).re| ≤ (A n).re + 2 * C * κ ^ n := by
      intro n
      rcases abs_cases (A n).re with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
        nlinarith [mul_nonneg hC (pow_nonneg hκ0 n)]
      · rw [h]
        have thisA : -(C * κ ^ n) ≤ (A n).re := by
          change -(C * κ ^ n) ≤
            (∑ i ∈ s, (w i : ℂ) * v i ^ (n + 1)).re
          exact hlow n
        nlinarith
    have hgeo : ∑ n ∈ Finset.range N, κ ^ n ≤ 1 / (1 - κ) := by
      have hκne : κ ≠ 1 := ne_of_lt hκ1
      rw [geom_sum_eq hκne]
      rw [show κ ^ N - 1 = -(1 - κ ^ N) by ring,
        show κ - 1 = -(1 - κ) by ring, neg_div_neg_eq]
      rw [div_le_div_iff₀ h1κ h1κ]
      nlinarith [pow_nonneg hκ0 N]
    calc
      ∑ n ∈ Finset.range N, ((A n).re) ^ 2 ≤
          ∑ n ∈ Finset.range N, K₁ * |(A n).re| := by
        refine Finset.sum_le_sum fun n _ => ?_
        have h1 : |(A n).re| ≤ K₁ :=
          le_trans (Complex.abs_re_le_norm _) (hAbound n)
        nlinarith [abs_nonneg ((A n).re), sq_abs ((A n).re)]
      _ = K₁ * ∑ n ∈ Finset.range N, |(A n).re| :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ K₁ * (C₁ + 2 * C / (1 - κ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK₁pos.le
        calc
          ∑ n ∈ Finset.range N, |(A n).re| ≤
              ∑ n ∈ Finset.range N, ((A n).re + 2 * C * κ ^ n) :=
                Finset.sum_le_sum fun n _ => habs n
          _ = (∑ n ∈ Finset.range N, A n).re +
                2 * C * ∑ n ∈ Finset.range N, κ ^ n := by
              rw [Finset.sum_add_distrib, Complex.re_sum, ← Finset.mul_sum]
          _ ≤ C₁ + 2 * C / (1 - κ) := by
            have h1 : (∑ n ∈ Finset.range N, A n).re ≤ C₁ :=
              le_trans (Complex.re_le_norm _) (hsum1 N)
            have h2 : 2 * C * ∑ n ∈ Finset.range N, κ ^ n ≤
                2 * C * (1 / (1 - κ)) :=
              mul_le_mul_of_nonneg_left hgeo (by positivity)
            have h3 : 2 * C * (1 / (1 - κ)) = 2 * C / (1 - κ) := by ring
            linarith
  have hlowN : ∀ N : ℕ, (K₂ * N - (C₄ + C₅)) / 2 ≤
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
    ((K₁ * (C₁ + 2 * C / (1 - κ)) * 2 + (C₄ + C₅)) / K₂)
  rw [div_lt_iff₀ hK₂pos] at hN
  have hfin1 := hlowN N
  have hfin2 := hup N
  nlinarith

end GaloisForLFunctions.HTGeometry

end
