import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.DirichletSeriesBounds
import GaloisForLFunctions.RHTower.Sieve.PerronInfiniteSeries
import GaloisForLFunctions.RHTower.Sieve.CesaroPerronReduction

/-! Near and far truncation errors for Mangoldt-majorized coefficients. -/

open Complex ArithmeticFunction MeasureTheory RHTower.Sieve

noncomputable section

namespace GlobalTheory.PerronPsi

theorem perron_hasSum (a : ℕ → ℂ) (ha0 : a 0 = 0) {c u T : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hT : 0 < T) (hs : LSeriesSummable a c) :
    HasSum (fun n : ℕ => a n * perronVertical c T (u / n))
      ((1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T,
        LSeries a ((c : ℂ) + t * I) * (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
  have hconv : Summable (fun n : ℕ => ‖a n‖ * (u / n) ^ c) := by
    refine ((summable_norm_iff.mpr hs).mul_right (u ^ c)).congr ?_
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0]
    · rw [LSeries.norm_term_eq, if_neg hn, ofReal_re, Real.div_rpow hu.le (Nat.cast_nonneg n)]
      ring
  have hsum : Summable (fun n : ℕ => a n * perronVertical c T (u / n)) := by
    refine Summable.of_norm_bounded (hconv.mul_right (T / (Real.pi * c))) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · rw [norm_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left
        ((norm_perronVertical_le_trivial (div_pos hu (by exact_mod_cast hn)) hc hT.le).trans_eq
          (by ring)) (norm_nonneg _)
  have he : (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        LSeries a ((c : ℂ) + t * I) * (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) =
        ∑' n : ℕ, a n * perronVertical c T (u / n) := by
    rw [← perron_tsum_integral_eq ha0 hu hc hT hconv]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_div_assoc]
    congr 1
    unfold LSeries
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0]
    · rw [LSeries.term_of_ne_zero hn, cpow_neg, div_eq_mul_inv]
  rw [he]
  exact hsum.hasSum

theorem zeta_bound {s : ℝ} (hs : 1 < s) : ∑' n : ℕ, 1 / (n : ℝ) ^ s ≤ 1 + 1 / (s - 1) := by
  have hsum := Real.summable_one_div_nat_rpow.mpr hs
  have hbound := GlobalTheory.Hk.LogDeriv.tsum_one_div_rpow_le hs
  rw [hsum.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : s ≠ 0), div_zero, zero_add]
  push_cast
  refine hbound.trans_eq ?_
  field_simp [ne_of_gt (sub_pos.mpr hs)]
  ring

noncomputable def w (N : ℕ) (B : ℝ) (n : ℕ) : ℝ :=
  (if n = N then 1 else 0) + (if n = N + 1 then 1 else 0)
    + B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ))

lemma w_nonneg (N : ℕ) {B : ℝ} (hB : 0 ≤ B) (n : ℕ) : 0 ≤ w N B n := by
  unfold w
  split_ifs <;> positivity

lemma harm (N : ℕ) : ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) ≤ 1 + Real.log N := by
  calc ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) = (harmonic N : ℝ) := by
        rw [Finset.sum_range_succ']
        simp [harmonic]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

lemma sum_w (N : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n ≤ 2 + B * (2 * (1 + Real.log N)) := by
  have hz1 : ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((N - n : ℕ) : ℝ)
      = ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) := by
    rw [Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range (N + 1), 1 / ((N - (N + 1 + x) : ℕ) : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [show N - (N + 1 + x) = 0 by omega]
      simp
    rw [h0, add_zero]
    have := Finset.sum_range_reflect (fun k : ℕ => 1 / (k : ℝ)) (N + 1)
    simpa using this
  have hz2 : ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((n - (N + 1) : ℕ) : ℝ)
      = ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) := by
    rw [Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range (N + 1), 1 / ((x - (N + 1) : ℕ) : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show x - (N + 1) = 0 by omega]
      simp
    rw [h0, zero_add]
    apply Finset.sum_congr rfl
    intro x _
    rw [show N + 1 + x - (N + 1) = x by omega]
  have hsplit : ∑ n ∈ Finset.range (N + 1 + (N + 1)), w N B n
      = (∑ n ∈ Finset.range (N + 1 + (N + 1)), (if n = N then (1 : ℝ) else 0))
        + (∑ n ∈ Finset.range (N + 1 + (N + 1)), (if n = N + 1 then (1 : ℝ) else 0))
        + B * (∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((N - n : ℕ) : ℝ)
          + ∑ n ∈ Finset.range (N + 1 + (N + 1)), 1 / ((n - (N + 1) : ℕ) : ℝ)) := by
    simp only [w, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  rw [hsplit, hz1, hz2]
  simp only [Finset.sum_ite_eq', Finset.mem_range, show N < N + 1 + (N + 1) by omega,
    show N + 1 < N + 1 + (N + 1) by omega, if_true]
  have h := harm N
  have h2 := mul_le_mul_of_nonneg_left
    (show ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ) + ∑ k ∈ Finset.range (N + 1), 1 / (k : ℝ)
      ≤ 2 * (1 + Real.log N) by linarith) hB
  linarith

lemma half_le_log {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by
  have h1 := Real.log_two_gt_d9
  have h2 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  linarith

lemma far_term {u T C E : ℝ} {n : ℕ} (hu : 2 ≤ u) (hT : 0 < T) (hn : 0 < n) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (h : E * (T * |Real.log (u / n)|) ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (hf : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n) :
    Real.log n * E ≤ C * (12 * u * Real.log u / T
      * (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)))) := by
  have hu0 : 0 < u := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL := half_le_log hu
  set L := Real.log u with hLdef
  have hL0 : 0 < L := by linarith
  set a := 1 / (2 * L) with ha
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have habs : 1 / 2 ≤ |Real.log (u / n)| := by
    rcases hf with hf | hf
    · have h2 : 2 ≤ u / n := by rw [le_div_iff₀ hn0]; linarith
      exact (half_le_log h2).trans (le_abs_self _)
    · have h2 : 2 ≤ n / u := by rw [le_div_iff₀ hu0]; linarith
      have h1 := half_le_log h2
      rw [Real.log_div hu0.ne' hn0.ne', abs_sub_comm, ← Real.log_div hn0.ne' hu0.ne']
      exact h1.trans (le_abs_self _)
  have key1 : E * T ≤ 2 * (C * (u / n) ^ (1 + 1 / L)) := by
    have h1 : E * (T * (1 / 2)) ≤ E * (T * |Real.log (u / n)|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hT.le) hE
    linarith
  have hQ : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn0 a
  have hP : 0 < (n : ℝ) ^ (1 + a) := Real.rpow_pos_of_pos hn0 _
  have hexp : 1 + a + a = 1 + 1 / L := by rw [ha]; ring
  have key2 : (u / n) ^ (1 + 1 / L) * ((n : ℝ) ^ (1 + a) * (n : ℝ) ^ a) = u * Real.exp 1 := by
    rw [← Real.rpow_add hn0, hexp, Real.div_rpow hu0.le hn0.le,
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos hn0 _).ne', Real.rpow_add hu0, Real.rpow_one,
      Real.rpow_def_of_pos hu0, ← hLdef, mul_one_div_cancel hL0.ne']
  have key3 : Real.log n ≤ 2 * L * (n : ℝ) ^ a := by
    have h1 := Real.log_le_sub_one_of_pos hQ
    rw [Real.log_rpow hn0] at h1
    have h2 : 2 * L * a = 1 := by rw [ha]; field_simp
    calc Real.log n = 2 * L * (a * Real.log n) := by rw [← mul_assoc, h2, one_mul]
      _ ≤ 2 * L * ((n : ℝ) ^ a - 1) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ 2 * L * (n : ℝ) ^ a := by nlinarith
  have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have hgoal : C * (12 * u * L / T * (1 / (n : ℝ) ^ (1 + a)))
      = (12 * C * u * L) / (T * (n : ℝ) ^ (1 + a)) := by
    field_simp
  rw [hgoal, le_div_iff₀ (mul_pos hT hP)]
  have h0 : 0 ≤ C * L * u := mul_nonneg (mul_nonneg hC hL0.le) hu0.le
  calc Real.log n * E * (T * (n : ℝ) ^ (1 + a)) = Real.log n * (E * T) * (n : ℝ) ^ (1 + a) := by ring
    _ ≤ (2 * L * (n : ℝ) ^ a) * (2 * (C * (u / n) ^ (1 + 1 / L))) * (n : ℝ) ^ (1 + a) := by
        apply mul_le_mul_of_nonneg_right _ hP.le
        exact mul_le_mul key3 key1 (mul_nonneg hE hT.le) (mul_nonneg (by linarith) hQ.le)
    _ = 4 * C * L * ((u / n) ^ (1 + 1 / L) * ((n : ℝ) ^ (1 + a) * (n : ℝ) ^ a)) := by ring
    _ = 4 * C * L * (u * Real.exp 1) := by rw [key2]
    _ ≤ 12 * C * u * L := by nlinarith

lemma near_term {u T C E : ℝ} {n : ℕ} (hu : 2 ≤ u) (hT : 0 < T) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (h0 : E ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (h : E * (T * |Real.log (u / n)|) ≤ C * (u / n) ^ (1 + 1 / Real.log u))
    (hf1 : u / 2 < n) (hf2 : n < 2 * u) :
    Real.log n * E ≤ C * (16 * Real.log u * w ⌊u⌋₊ (2 * u / T) n) := by
  have hu0 : 0 < u := by linarith
  have hL := half_le_log hu
  set L := Real.log u with hLdef
  have hL0 : 0 < L := by linarith
  set N := ⌊u⌋₊ with hN
  set B := 2 * u / T with hB
  have hB0 : 0 ≤ B := div_nonneg (by linarith) hT.le
  have hn1 : (1 : ℝ) < n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1.le
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hu
  have hlogn : Real.log n ≤ 2 * L := by
    have h2 : Real.log n ≤ Real.log (2 * u) := Real.log_le_log hn0 hf2.le
    rw [Real.log_mul (by norm_num) hu0.ne'] at h2
    linarith
  have hM : (u / n) ^ (1 + 1 / L) ≤ 6 := by
    have hr : u / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
    have hσ : 0 ≤ 1 + 1 / L := by have := one_div_pos.2 hL0; linarith
    calc (u / n) ^ (1 + 1 / L) ≤ (2 : ℝ) ^ (1 + 1 / L) :=
          Real.rpow_le_rpow (div_nonneg hu0.le hn0.le) hr hσ
      _ = 2 * Real.exp (Real.log 2 * (1 / L)) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_def_of_pos (by norm_num)]
      _ ≤ 2 * Real.exp 1 := by
          gcongr
          rw [mul_one_div, div_le_one hL0]
          exact hlog2
      _ ≤ 6 := by have := Real.exp_one_lt_d9; linarith
  have hCM : C * (u / n) ^ (1 + 1 / L) ≤ 6 * C := by
    have := mul_le_mul_of_nonneg_left hM hC
    linarith
  have hCL : 0 ≤ C * L := mul_nonneg hC hL0.le
  have hwdef : w N B n = (if n = N then 1 else 0) + (if n = N + 1 then 1 else 0)
      + B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ)) := rfl
  have hrest : 0 ≤ B * (1 / ((N - n : ℕ) : ℝ) + 1 / ((n - (N + 1) : ℕ) : ℝ)) :=
    mul_nonneg hB0 (by positivity)
  have caseA : 1 ≤ w N B n → Real.log n * E ≤ C * (16 * L * w N B n) := by
    intro hw1
    have h1 : Real.log n * E ≤ 2 * L * (6 * C) :=
      mul_le_mul hlogn (h0.trans hCM) hE (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hw1 hCL]
  have core : ∀ k : ℝ, 0 < k → k / (2 * u) ≤ |Real.log (u / n)| → B * (1 / k) ≤ w N B n →
      Real.log n * E ≤ C * (16 * L * w N B n) := by
    intro k hk hlog hwk
    have h1 : E * (T * (k / (2 * u))) ≤ 6 * C :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog hT.le) hE) (h.trans hCM)
    have h2 : E * k = E * (T * (k / (2 * u))) * B := by
      rw [hB]
      field_simp
    have h3 : E * k ≤ 6 * C * B := by
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 hB0
    have h4 : Real.log n * E * k ≤ 2 * L * (6 * C * B) := by
      rw [mul_assoc]
      exact mul_le_mul hlogn h3 (mul_nonneg hE hk.le) (by linarith)
    have h5 : Real.log n * E ≤ 12 * C * L * (B * (1 / k)) := by
      rw [show 12 * C * L * (B * (1 / k)) = (12 * C * L * B) / k by ring, le_div_iff₀ hk]
      linarith
    have hbk : 0 ≤ B * (1 / k) := mul_nonneg hB0 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hwk hCL, mul_nonneg hCL hbk]
  have hNu : (N : ℝ) ≤ u := Nat.floor_le hu0.le
  have huN : u < (N : ℝ) + 1 := Nat.lt_floor_add_one u
  rcases lt_trichotomy n N with hlt | heq | hgt
  · have hlt' : (n : ℝ) < N := by exact_mod_cast hlt
    have hk : (0 : ℝ) < (N : ℝ) - n := sub_pos.2 hlt'
    apply core ((N : ℝ) - n) hk
    · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hu0 hn0)
      rw [inv_div] at h1
      have e1 : 1 - n / u = (u - n) / u := by field_simp
      have e2 : ((N : ℝ) - n) / (2 * u) ≤ (u - n) / (2 * u) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
      have e3 : (u - n) / (2 * u) ≤ (u - n) / u :=
        div_le_div_of_nonneg_left (by linarith) hu0 (by linarith)
      rw [e1] at h1
      exact e2.trans (e3.trans (h1.trans (le_abs_self _)))
    · have hcast : ((N - n : ℕ) : ℝ) = (N : ℝ) - n := Nat.cast_sub hlt.le
      rw [hwdef, hcast, if_neg hlt.ne, if_neg (by omega), mul_add]
      have : 0 ≤ B * (1 / ((n - (N + 1) : ℕ) : ℝ)) := mul_nonneg hB0 (by positivity)
      linarith
  · apply caseA
    rw [hwdef, if_pos heq]
    have : (0 : ℝ) ≤ if n = N + 1 then 1 else 0 := by split_ifs <;> norm_num
    linarith
  · rcases Nat.lt_or_ge (N + 1) n with hgt2 | hle
    · have hgt2' : (N : ℝ) + 1 < n := by exact_mod_cast hgt2
      have hk : (0 : ℝ) < (n : ℝ) - (N + 1) := by linarith
      apply core ((n : ℝ) - (N + 1)) hk
      · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hu0)
        rw [inv_div] at h1
        have e1 : 1 - u / n = (n - u) / n := by field_simp
        have e2 : ((n : ℝ) - (N + 1)) / (2 * u) ≤ (n - u) / (2 * u) :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
        have e3 : ((n : ℝ) - u) / (2 * u) ≤ (n - u) / n :=
          div_le_div_of_nonneg_left (by linarith) hn0 hf2.le
        rw [e1] at h1
        have habs : Real.log (n / u) ≤ |Real.log (u / n)| := by
          rw [Real.log_div hu0.ne' hn0.ne', abs_sub_comm, ← Real.log_div hn0.ne' hu0.ne']
          exact le_abs_self _
        exact e2.trans (e3.trans (h1.trans habs))
      · have hcast : ((n - (N + 1) : ℕ) : ℝ) = (n : ℝ) - (N + 1) := by
          rw [Nat.cast_sub hgt2.le]
          push_cast
          ring
        rw [hwdef, hcast, if_neg (by omega), if_neg (by omega), mul_add]
        have : 0 ≤ B * (1 / ((N - n : ℕ) : ℝ)) := mul_nonneg hB0 (by positivity)
        linarith
    · have heq1 : n = N + 1 := by omega
      apply caseA
      rw [hwdef, if_neg (by omega), if_pos heq1]
      linarith

end GlobalTheory.PerronPsi
