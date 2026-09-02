import GaloisForLFunctions.RHTower.PositiveSchattenLogResidueTraceClassPerturbation

namespace RHTower

open _root_.ContinuousLinearMap Filter Finset
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The left singular coefficients form an `ℓ²` sequence. -/
theorem summable_inner_svdVec_sq {T : H →L[ℂ] H}
    (hcpt : IsCompactOperator T) (x : H) :
    Summable (fun n => ‖inner ℂ x (svdVec T n)‖ ^ 2) := by
  have hunit : ∀ n, svdVec T n = 0 ∨ ‖svdVec T n‖ = 1 := by
    intro n
    rcases eq_or_ne (singVal T n) 0 with h0 | hne
    · exact Or.inl (svdVec_eq_zero_of_singVal_eq_zero _ h0)
    · exact Or.inr (norm_svdVec_sq hcpt hne)
  have horth : ∀ m n, m ≠ n → inner ℂ (svdVec T m) (svdVec T n) = 0 :=
    fun m n hmn => inner_svdVec_svdVec_of_ne T hmn
  apply summable_of_sum_le (fun n => sq_nonneg ‖inner ℂ x (svdVec T n)‖)
  intro s
  have hflip : ∀ n, ‖inner ℂ x (svdVec T n)‖ =
      ‖inner ℂ (svdVec T n) x‖ := by
    intro n
    rw [← inner_conj_symm, RCLike.norm_conj]
  rw [Finset.sum_congr rfl (fun n _ => by rw [hflip n])]
  exact sum_inner_sq_le_of_orthonormal_with_zeros
    (svdVec T) hunit horth x s

/-- Bessel bound for the left singular coefficients. -/
theorem tsum_inner_svdVec_sq_le {T : H →L[ℂ] H}
    (hcpt : IsCompactOperator T) (x : H) :
    ∑' n, ‖inner ℂ x (svdVec T n)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  apply Real.tsum_le_of_sum_le (fun n => sq_nonneg ‖inner ℂ x (svdVec T n)‖)
  intro s
  have hunit : ∀ n, svdVec T n = 0 ∨ ‖svdVec T n‖ = 1 := by
    intro n
    rcases eq_or_ne (singVal T n) 0 with h0 | hne
    · exact Or.inl (svdVec_eq_zero_of_singVal_eq_zero _ h0)
    · exact Or.inr (norm_svdVec_sq hcpt hne)
  have horth : ∀ m n, m ≠ n → inner ℂ (svdVec T m) (svdVec T n) = 0 :=
    fun m n hmn => inner_svdVec_svdVec_of_ne T hmn
  have hflip : ∀ n, ‖inner ℂ x (svdVec T n)‖ =
      ‖inner ℂ (svdVec T n) x‖ := by
    intro n
    rw [← inner_conj_symm, RCLike.norm_conj]
  rw [Finset.sum_congr rfl (fun n _ => by rw [hflip n])]
  exact sum_inner_sq_le_of_orthonormal_with_zeros
    (svdVec T) hunit horth x s

/-- Products of right and left singular coefficients are summable. -/
theorem summable_svdPairCoefficient {T : H →L[ℂ] H}
    (hcpt : IsCompactOperator T) (x y : H) :
    Summable (fun n =>
      ‖inner ℂ (svVec (energyOp T) n) x‖ *
        ‖inner ℂ y (svdVec T n)‖) := by
  have ha : Summable (fun n =>
      ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2) :=
    summable_inner_svVec_sq hcpt x
  have hb : Summable (fun n => ‖inner ℂ y (svdVec T n)‖ ^ 2) :=
    summable_inner_svdVec_sq hcpt y
  have hmajor : Summable (fun n =>
      (‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 +
        ‖inner ℂ y (svdVec T n)‖ ^ 2) / 2) := by
    simpa [div_eq_mul_inv, add_mul] using (ha.add hb).mul_right (2 : ℝ)⁻¹
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun n => ?_) hmajor
  nlinarith [sq_nonneg
    (‖inner ℂ (svVec (energyOp T) n) x‖ - ‖inner ℂ y (svdVec T n)‖)]

/-- Unit vectors give total paired singular coefficient mass at most one. -/
theorem tsum_svdPairCoefficient_le_one {T : H →L[ℂ] H}
    (hcpt : IsCompactOperator T) {x y : H}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∑' n, ‖inner ℂ (svVec (energyOp T) n) x‖ *
        ‖inner ℂ y (svdVec T n)‖ ≤ 1 := by
  have ha : Summable (fun n =>
      ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2) :=
    summable_inner_svVec_sq hcpt x
  have hb : Summable (fun n => ‖inner ℂ y (svdVec T n)‖ ^ 2) :=
    summable_inner_svdVec_sq hcpt y
  have hp := summable_svdPairCoefficient hcpt x y
  have hterm : ∀ n,
      ‖inner ℂ (svVec (energyOp T) n) x‖ * ‖inner ℂ y (svdVec T n)‖ ≤
        (‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 +
          ‖inner ℂ y (svdVec T n)‖ ^ 2) / 2 := by
    intro n
    nlinarith [sq_nonneg
      (‖inner ℂ (svVec (energyOp T) n) x‖ - ‖inner ℂ y (svdVec T n)‖)]
  have hmajor : Summable (fun n =>
      (‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 +
        ‖inner ℂ y (svdVec T n)‖ ^ 2) / 2) := by
    simpa [div_eq_mul_inv, add_mul] using (ha.add hb).mul_right (2 : ℝ)⁻¹
  calc
    (∑' n, ‖inner ℂ (svVec (energyOp T) n) x‖ *
        ‖inner ℂ y (svdVec T n)‖) ≤
        ∑' n, (‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2 +
          ‖inner ℂ y (svdVec T n)‖ ^ 2) / 2 :=
      hp.tsum_le_tsum hterm hmajor
    _ = ((∑' n, ‖inner ℂ (svVec (energyOp T) n) x‖ ^ 2) +
          ∑' n, ‖inner ℂ y (svdVec T n)‖ ^ 2) / 2 := by
      rw [tsum_div_const, ha.tsum_add hb]
    _ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
      gcongr
      · exact tsum_inner_svVec_sq_le hcpt x
      · exact tsum_inner_svdVec_sq_le hcpt y
    _ ≤ 1 := by nlinarith [norm_nonneg x, norm_nonneg y]

/-- Ky Fan variational inequality for two orthonormal-with-zero families. -/
theorem sum_norm_inner_le_sum_singVal
    {T : H →L[ℂ] H} (hcpt : IsCompactOperator T)
    {ι : Type*} {g h : ι → H}
    (hg1 : ∀ n, g n = 0 ∨ ‖g n‖ = 1)
    (hgo : ∀ m n, m ≠ n → inner ℂ (g m) (g n) = 0)
    (hh1 : ∀ n, h n = 0 ∨ ‖h n‖ = 1)
    (hho : ∀ m n, m ≠ n → inner ℂ (h m) (h n) = 0)
    (s : Finset ι) {N : ℕ} (hcard : s.card ≤ N) :
    ∑ n ∈ s, ‖inner ℂ (g n) (T (h n))‖ ≤
      ∑ k ∈ Finset.range N, singVal T k := by
  classical
  have hnorm_le_one : ∀ (v : ι → H),
      (∀ n, v n = 0 ∨ ‖v n‖ = 1) → ∀ n, ‖v n‖ ≤ 1 := by
    intro v hv n
    rcases hv n with h0 | h1
    · rw [h0, norm_zero]; norm_num
    · rw [h1]
  have hpair : ∀ n, HasSum
      (fun k => (((singVal T k : ℝ) : ℂ) *
        inner ℂ (svVec (energyOp T) k) (h n)) *
          inner ℂ (g n) (svdVec T k))
      (inner ℂ (g n) (T (h n))) := by
    intro n
    have h1 := (hasSum_svd hcpt (h n)).mapL (innerSL ℂ (g n))
    simpa only [innerSL_apply_apply, inner_smul_right, mul_comm] using h1
  set c : ℕ → ℝ := fun k =>
    ∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) k) (h n)‖ *
      ‖inner ℂ (g n) (svdVec T k)‖ with hc
  have hprodSummable : ∀ n, Summable (fun k =>
      ‖inner ℂ (svVec (energyOp T) k) (h n)‖ *
        ‖inner ℂ (g n) (svdVec T k)‖) := fun n =>
    summable_svdPairCoefficient hcpt (h n) (g n)
  have hcsum : Summable c := by
    rw [hc]
    exact summable_sum fun n _ => hprodSummable n
  have hc0 : ∀ k, 0 ≤ c k := fun k => by
    rw [hc]
    positivity
  have hc1 : ∀ k, c k ≤ 1 := by
    intro k
    rw [hc]
    have hCS : ∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) k) (h n)‖
          * ‖inner ℂ (g n) (svdVec T k)‖
        ≤ Real.sqrt (∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) k) (h n)‖ ^ 2)
          * Real.sqrt (∑ n ∈ s, ‖inner ℂ (g n) (svdVec T k)‖ ^ 2) := by
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq s
        (fun n => ‖inner ℂ (svVec (energyOp T) k) (h n)‖)
        (fun n => ‖inner ℂ (g n) (svdVec T k)‖)
      have h2 : 0 ≤ ∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) k) (h n)‖
          * ‖inner ℂ (g n) (svdVec T k)‖ := Finset.sum_nonneg fun n _ => by positivity
      calc
        _ = Real.sqrt ((∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) k) (h n)‖
              * ‖inner ℂ (g n) (svdVec T k)‖) ^ 2) := (Real.sqrt_sq h2).symm
        _ ≤ Real.sqrt ((∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) k) (h n)‖ ^ 2)
              * ∑ n ∈ s, ‖inner ℂ (g n) (svdVec T k)‖ ^ 2) := Real.sqrt_le_sqrt h1
        _ = _ := Real.sqrt_mul (Finset.sum_nonneg fun n _ => by positivity) _
    have hB1 : ∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) k) (h n)‖ ^ 2 ≤ 1 := by
      have hflip : ∀ n, ‖inner ℂ (svVec (energyOp T) k) (h n)‖ =
          ‖inner ℂ (h n) (svVec (energyOp T) k)‖ := by
        intro n
        rw [← inner_conj_symm, RCLike.norm_conj]
      rw [Finset.sum_congr rfl (fun n _ => by rw [hflip n])]
      exact (sum_inner_sq_le_of_orthonormal_with_zeros h hh1 hho _ s).trans
        (by
          rcases eq_or_ne (svVal (energyOp T) k) 0 with h0 | hne
          · rw [svVec_eq_zero_of_svVal_eq_zero _ h0, norm_zero]; norm_num
          · rw [norm_svVec_of_ne_zero (energyOp_compact hcpt)
              (energyOp_symmetric T) (energyOp_pos T) hne]
            norm_num)
    have hB2 : ∑ n ∈ s, ‖inner ℂ (g n) (svdVec T k)‖ ^ 2 ≤ 1 := by
      exact (sum_inner_sq_le_of_orthonormal_with_zeros g hg1 hgo _ s).trans
        (by
          rcases eq_or_ne (singVal T k) 0 with h0 | hne
          · rw [svdVec_eq_zero_of_singVal_eq_zero _ h0, norm_zero]; norm_num
          · rw [norm_svdVec_sq hcpt hne]; norm_num)
    calc
      _ ≤ Real.sqrt (∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) k) (h n)‖ ^ 2)
          * Real.sqrt (∑ n ∈ s, ‖inner ℂ (g n) (svdVec T k)‖ ^ 2) := hCS
      _ ≤ Real.sqrt 1 * Real.sqrt 1 := by gcongr
      _ = 1 := by norm_num
  have hmass : ∑' k, c k ≤ (N : ℝ) := by
    rw [hc, Summable.tsum_finsetSum (fun n _ => hprodSummable n)]
    calc
      (∑ n ∈ s, ∑' k,
          ‖inner ℂ (svVec (energyOp T) k) (h n)‖ *
            ‖inner ℂ (g n) (svdVec T k)‖) ≤ ∑ n ∈ s, 1 := by
        apply Finset.sum_le_sum
        intro n hn
        exact tsum_svdPairCoefficient_le_one hcpt
          (hnorm_le_one h hh1 n) (hnorm_le_one g hg1 n)
      _ = s.card := by simp
      _ ≤ N := by exact_mod_cast hcard
  have hμcsum : Summable (fun k => singVal T k * c k) := by
    rw [hc]
    have hrewrite : (fun k => singVal T k *
        ∑ n ∈ s, ‖inner ℂ (svVec (energyOp T) k) (h n)‖ *
          ‖inner ℂ (g n) (svdVec T k)‖) =
        fun k => ∑ n ∈ s, singVal T k *
          (‖inner ℂ (svVec (energyOp T) k) (h n)‖ *
            ‖inner ℂ (g n) (svdVec T k)‖) := by
      funext k
      rw [Finset.mul_sum]
    rw [hrewrite]
    apply summable_sum
    intro n hn
    have hp := hprodSummable n
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (singVal_nonneg T k) (by positivity))
      (fun k => ?_) (hp.mul_left ‖T‖)
    have hsle : singVal T k ≤ ‖T‖ := by
      rw [← approxNumber_eq_singVal hcpt]
      exact approxNumber_le_norm T k
    exact mul_le_mul_of_nonneg_right hsle (by positivity)
  have hbound : ∀ n, ‖inner ℂ (g n) (T (h n))‖ ≤
      ∑' k, singVal T k *
        (‖inner ℂ (svVec (energyOp T) k) (h n)‖ *
          ‖inner ℂ (g n) (svdVec T k)‖) := by
    intro n
    have hsummable_norm : Summable (fun k =>
        ‖(((singVal T k : ℝ) : ℂ) * inner ℂ (svVec (energyOp T) k) (h n))
          * inner ℂ (g n) (svdVec T k)‖) := by
      apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
        (fun k => ?_) ((hprodSummable n).mul_left ‖T‖)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (singVal_nonneg T k), mul_assoc]
      have hsle : singVal T k ≤ ‖T‖ := by
        rw [← approxNumber_eq_singVal hcpt]
        exact approxNumber_le_norm T k
      exact mul_le_mul_of_nonneg_right hsle (by positivity)
    calc
      ‖inner ℂ (g n) (T (h n))‖ =
          ‖∑' k, (((singVal T k : ℝ) : ℂ) *
            inner ℂ (svVec (energyOp T) k) (h n)) *
              inner ℂ (g n) (svdVec T k)‖ := by rw [(hpair n).tsum_eq]
      _ ≤ ∑' k, ‖(((singVal T k : ℝ) : ℂ) *
            inner ℂ (svVec (energyOp T) k) (h n)) *
              inner ℂ (g n) (svdVec T k)‖ := norm_tsum_le_tsum_norm hsummable_norm
      _ = _ := by
        apply tsum_congr
        intro k
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (singVal_nonneg T k), mul_assoc]
  have hweightedSummable : ∀ n, Summable (fun k => singVal T k *
      (‖inner ℂ (svVec (energyOp T) k) (h n)‖ *
        ‖inner ℂ (g n) (svdVec T k)‖)) := by
    intro n
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (singVal_nonneg T k) (by positivity))
      (fun k => ?_) ((hprodSummable n).mul_left ‖T‖)
    have hsle : singVal T k ≤ ‖T‖ := by
      rw [← approxNumber_eq_singVal hcpt]
      exact approxNumber_le_norm T k
    exact mul_le_mul_of_nonneg_right hsle (by positivity)
  calc
    ∑ n ∈ s, ‖inner ℂ (g n) (T (h n))‖ ≤
        ∑ n ∈ s, ∑' k, singVal T k *
          (‖inner ℂ (svVec (energyOp T) k) (h n)‖ *
            ‖inner ℂ (g n) (svdVec T k)‖) :=
      Finset.sum_le_sum fun n _ => hbound n
    _ = ∑' k, ∑ n ∈ s, singVal T k *
          (‖inner ℂ (svVec (energyOp T) k) (h n)‖ *
            ‖inner ℂ (g n) (svdVec T k)‖) :=
      (Summable.tsum_finsetSum fun n _ => hweightedSummable n).symm
    _ = ∑' k, singVal T k * c k := by
      apply tsum_congr
      intro k
      rw [hc, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range N, singVal T k :=
      tsum_mul_le_sum_range_of_antitone (singVal_nonneg T) (singVal_antitone T)
        hc0 hc1 hcsum hμcsum N hmass

/-- One-sided Ky Fan--Mirsky comparison under an arbitrary trace-class perturbation. -/
theorem schattenPowerPartialSum_one_le_add_traceNorm_of_traceClass_sub
    {A B : H →L[ℂ] H}
    (hAcpt : IsCompactOperator A) (hBcpt : IsCompactOperator B)
    (hAB : MemSchattenClass 1 (A - B)) (N : ℕ) :
    schattenPowerPartialSum 1 A N ≤
      schattenPowerPartialSum 1 B N + traceNorm H (A - B) := by
  let e : ℕ → H := fun n => svVec (energyOp A) n
  let f : ℕ → H := fun n => svdVec A n
  have he : ∀ n, e n = 0 ∨ ‖e n‖ = 1 := by
    intro n
    rcases eq_or_ne (svVal (energyOp A) n) 0 with h0 | hne
    · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ h0)
    · exact Or.inr
        (norm_svVec_of_ne_zero (energyOp_compact hAcpt)
          (energyOp_symmetric A) (energyOp_pos A) hne)
  have hf : ∀ n, f n = 0 ∨ ‖f n‖ = 1 := by
    intro n
    rcases eq_or_ne (singVal A n) 0 with h0 | hne
    · exact Or.inl (svdVec_eq_zero_of_singVal_eq_zero _ h0)
    · exact Or.inr (norm_svdVec_sq hAcpt hne)
  have heorth : ∀ m n, m ≠ n → inner ℂ (e m) (e n) = 0 := fun m n hmn =>
    inner_svVec_svVec_of_ne _ hmn
  have hforth : ∀ m n, m ≠ n → inner ℂ (f m) (f n) = 0 := fun m n hmn =>
    inner_svdVec_svdVec_of_ne _ hmn
  have hdiagA : schattenPowerPartialSum 1 A N =
      ∑ n ∈ Finset.range N, RCLike.re (inner ℂ (f n) (A (e n)) : ℂ) := by
    unfold schattenPowerPartialSum
    apply Finset.sum_congr rfl
    intro n hn
    rw [Real.rpow_one, approxNumber_eq_singVal hAcpt]
    dsimp [f, e]
    rw [inner_svdVec_apply hAcpt]
    simp
  have hdiagB : (∑ n ∈ Finset.range N,
      RCLike.re (inner ℂ (f n) (B (e n)) : ℂ)) ≤
      schattenPowerPartialSum 1 B N := by
    calc
      (∑ n ∈ Finset.range N,
          RCLike.re (inner ℂ (f n) (B (e n)) : ℂ)) ≤
          ∑ n ∈ Finset.range N, ‖inner ℂ (f n) (B (e n))‖ :=
        Finset.sum_le_sum fun n _ => RCLike.re_le_norm _
      _ ≤ ∑ k ∈ Finset.range N, singVal B k :=
        sum_norm_inner_le_sum_singVal hBcpt hf hforth he heorth
          (Finset.range N) (by simp)
      _ = schattenPowerPartialSum 1 B N := by
        unfold schattenPowerPartialSum
        apply Finset.sum_congr rfl
        intro n hn
        rw [Real.rpow_one, approxNumber_eq_singVal hBcpt]
  have hABcpt : IsCompactOperator (A - B) := hAB.isCompactOperator one_pos
  have hdiff : (∑ n ∈ Finset.range N,
      ‖inner ℂ (f n) ((A - B) (e n))‖) ≤ traceNorm H (A - B) :=
    sum_norm_inner_le_traceNorm hABcpt hAB.one_summable
      hf hforth he heorth (Finset.range N)
  rw [hdiagA]
  have hsplit : (∑ n ∈ Finset.range N,
      RCLike.re (inner ℂ (f n) (A (e n)) : ℂ)) =
      (∑ n ∈ Finset.range N,
        RCLike.re (inner ℂ (f n) (B (e n)) : ℂ)) +
      ∑ n ∈ Finset.range N,
        RCLike.re (inner ℂ (f n) ((A - B) (e n)) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [sub_apply, inner_sub_right, map_sub]
    ring
  rw [hsplit]
  calc
    (∑ n ∈ Finset.range N,
        RCLike.re (inner ℂ (f n) (B (e n)) : ℂ)) +
        ∑ n ∈ Finset.range N,
          RCLike.re (inner ℂ (f n) ((A - B) (e n)) : ℂ) ≤
      (∑ n ∈ Finset.range N,
        RCLike.re (inner ℂ (f n) (B (e n)) : ℂ)) +
        ∑ n ∈ Finset.range N,
          ‖inner ℂ (f n) ((A - B) (e n))‖ := by
      exact add_le_add (le_refl _)
        (Finset.sum_le_sum fun n _ => RCLike.re_le_norm _)
    _ ≤ schattenPowerPartialSum 1 B N + traceNorm H (A - B) :=
      add_le_add hdiagB hdiff

/-- Arbitrary trace-class perturbations change every Schatten-one prefix by at most their trace
norm. -/
theorem abs_schattenPowerPartialSum_one_sub_le_traceNorm_of_traceClass_sub
    {A B : H →L[ℂ] H}
    (hAcpt : IsCompactOperator A) (hBcpt : IsCompactOperator B)
    (hAB : MemSchattenClass 1 (A - B)) (N : ℕ) :
    |schattenPowerPartialSum 1 A N - schattenPowerPartialSum 1 B N| ≤
      traceNorm H (A - B) := by
  have hupper := schattenPowerPartialSum_one_le_add_traceNorm_of_traceClass_sub
    hAcpt hBcpt hAB N
  have hBA : MemSchattenClass 1 (B - A) := by
    have h := hAB.one_neg
    simpa [show -(A - B) = B - A by abel] using h
  have hlower := schattenPowerPartialSum_one_le_add_traceNorm_of_traceClass_sub
    hBcpt hAcpt hBA N
  have hnormNeg : traceNorm H (B - A) = traceNorm H (A - B) := by
    have h := traceNorm_smul (-1 : ℂ) (A - B)
    simpa [show (-1 : ℂ) • (A - B) = B - A by module] using h
  rw [hnormNeg] at hlower
  rw [abs_le]
  constructor <;> linarith

/-- Logarithmically normalized Schatten-one prefixes of arbitrary trace-class perturbations differ
by `o(1)`. -/
theorem tendsto_schattenPowerPartialSum_one_div_log_sub_of_traceClass
    {A B : H →L[ℂ] H}
    (hAcpt : IsCompactOperator A) (hBcpt : IsCompactOperator B)
    (hAB : MemSchattenClass 1 (A - B)) :
    Tendsto (fun N : ℕ =>
      schattenPowerPartialSum 1 A N / Real.log (N + 1) -
        schattenPowerPartialSum 1 B N / Real.log (N + 1)) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hzero : Tendsto (fun N : ℕ => traceNorm H (A - B) / Real.log (N + 1))
      atTop (nhds 0) := hlog.const_div_atTop _
  refine squeeze_zero_norm' (a := fun N : ℕ =>
    traceNorm H (A - B) / Real.log (N + 1)) ?_ hzero
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hlogPos : 0 < Real.log (N + 1) :=
    Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hN)
  rw [← sub_div]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlogPos]
  exact (div_le_div_iff_of_pos_right hlogPos).2
    (abs_schattenPowerPartialSum_one_sub_le_traceNorm_of_traceClass_sub
      hAcpt hBcpt hAB N)

/-- Existence and value of the logarithmic Schatten-one residue are invariant under arbitrary
trace-class perturbations; no positivity or self-adjointness is required. -/
theorem hasSchattenLogResidue_one_iff_of_traceClass_sub
    {A B : H →L[ℂ] H}
    (hAcpt : IsCompactOperator A) (hBcpt : IsCompactOperator B)
    (hAB : MemSchattenClass 1 (A - B)) (R : ℝ) :
    HasSchattenLogResidue 1 A R ↔ HasSchattenLogResidue 1 B R := by
  let fA := fun N : ℕ => schattenPowerPartialSum 1 A N / Real.log (N + 1)
  let fB := fun N : ℕ => schattenPowerPartialSum 1 B N / Real.log (N + 1)
  have hdiff : Tendsto (fun N => fA N - fB N) atTop (nhds 0) := by
    simpa [fA, fB] using
      tendsto_schattenPowerPartialSum_one_div_log_sub_of_traceClass
        hAcpt hBcpt hAB
  constructor
  · intro hA
    have h := hA.sub hdiff
    rw [sub_zero] at h
    exact h.congr fun N => by simp [fA, fB]
  · intro hB
    have h := hB.add hdiff
    rw [add_zero] at h
    exact h.congr fun N => by simp [fA, fB]

/-- Additive form of arbitrary trace-class perturbation invariance. -/
theorem hasSchattenLogResidue_one_add_iff_of_memSchattenClass_one
    {A T : H →L[ℂ] H} (hAcpt : IsCompactOperator A)
    (hT : MemSchattenClass 1 T) (R : ℝ) :
    HasSchattenLogResidue 1 (A + T) R ↔ HasSchattenLogResidue 1 A R := by
  have hTcpt : IsCompactOperator T := hT.isCompactOperator one_pos
  apply hasSchattenLogResidue_one_iff_of_traceClass_sub
    (hAcpt.add hTcpt) hAcpt
  simpa using hT

end

end RHTower
