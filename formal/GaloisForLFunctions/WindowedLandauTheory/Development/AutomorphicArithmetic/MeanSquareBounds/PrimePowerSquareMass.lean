import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimePowerWeights
import GaloisForLFunctions.RHTower.Sieve.Mertens

/-! The prime-power diagonal has squared mass bounded by a constant times `y log y`. -/

open Finset Classical

noncomputable section

namespace QH

private theorem sum_log_primes_le_mul_log_four (Y : ℕ) :
    ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ Y * Real.log 4 := by
  rw [show (range (Y + 1)).filter Nat.Prime = Nat.primesLE Y from by
    ext p
    simp only [mem_filter, mem_range, Nat.mem_primesLE, Nat.lt_succ_iff]]
  exact RHTower.Sieve.sum_log_primesLE_le Y

theorem sum_log_sq_div_sq_primes_dyadic_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      2 * Real.log 4 * Real.log (2 * y) / y := by
  have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0:ℝ) < y := by linarith
  have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
  have hL0 : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hy2pos : 0 < (y:ℝ) ^ 2 := by positivity
  have hterm : ∀ p ∈ (Ioc y (2 * y)).filter Nat.Prime,
      Real.log p ^ 2 / (p : ℝ) ^ 2 ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hpr⟩ := hp
    have hp1 : (y:ℝ) < p := by exact_mod_cast h1
    have hp2 : (p:ℝ) ≤ 2 * y := by exact_mod_cast h2
    have hppos : (0:ℝ) < p := by linarith
    have hp2pos : 0 < (p:ℝ) ^ 2 := by positivity
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    have hlle : Real.log p ≤ Real.log (2 * y) := Real.log_le_log hppos hp2
    have hyp : (y:ℝ) ^ 2 ≤ (p:ℝ) ^ 2 := pow_le_pow_left₀ hy0.le hp1.le 2
    have hnum : 0 ≤ Real.log (2 * y) * Real.log p := mul_nonneg hL0 hlp
    calc Real.log p ^ 2 / (p:ℝ) ^ 2 = Real.log p * Real.log p / (p:ℝ) ^ 2 := by ring
      _ ≤ Real.log (2 * y) * Real.log p / (p:ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlle hlp) hp2pos.le
      _ ≤ Real.log (2 * y) * Real.log p / (y:ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_left hnum hy2pos hyp
      _ = Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by ring
  have hsum : ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ≤ 2 * y * Real.log 4 := by
    have hsub : (Ioc y (2 * y)).filter Nat.Prime ⊆ (Finset.range (2 * y + 1)).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp.2⟩
    calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p
        ≤ ∑ p ∈ (Finset.range (2 * y + 1)).filter Nat.Prime, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
      _ ≤ 2 * y * Real.log 4 := by
          exact_mod_cast sum_log_primes_le_mul_log_four (2 * y)
  calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
      ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p :=
        Finset.sum_le_sum hterm
    _ = Real.log (2 * y) / (y:ℝ) ^ 2 * ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p := by
        rw [Finset.mul_sum]
    _ ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * (2 * y * Real.log 4) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hL0 (sq_nonneg _))
    _ = 2 * Real.log 4 * Real.log (2 * y) / y := by
        field_simp

theorem sum_log_sq_div_sq_primes_tail_le (N : ℕ) : ∀ d y : ℕ, 1 ≤ y → N - y ≤ d →
    ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
  intro d
  induction d with
  | zero =>
    intro y hy hd
    have hN : N ≤ y := by omega
    rw [Finset.Ioc_eq_empty_of_le hN, Finset.filter_empty, Finset.sum_empty]
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) h4) (by linarith)) (by positivity)
  | succ d ih =>
    intro y hy hd
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have hy0 : (0:ℝ) < y := by linarith
    have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
      Real.log_mul (by norm_num) hy0'
    have hblock := sum_log_sq_div_sq_primes_dyadic_le y hy
    by_cases hN : N ≤ 2 * y
    · have hsub : (Ioc y N).filter Nat.Prime ⊆ (Ioc y (2 * y)).filter Nat.Prime :=
        Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hN)
      calc ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ ≤ 2 * Real.log 4 * Real.log (2 * y) / y := hblock
        _ ≤ 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            gcongr ?_ / _
            rw [hlog2y]
            nlinarith [mul_nonneg hl4 hly, mul_nonneg hl4 hl2]
    · push Not at hN
      have hsplit : (Ioc y N).filter Nat.Prime =
          (Ioc y (2 * y)).filter Nat.Prime ∪ (Ioc (2 * y) N).filter Nat.Prime := by
        rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (by omega) hN.le]
      have hdisj : Disjoint ((Ioc y (2 * y)).filter Nat.Prime) ((Ioc (2 * y) N).filter Nat.Prime) := by
        apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_Ioc] at ha hb
        omega
      have ht := ih (2 * y) (by omega) (by omega)
      rw [hsplit, Finset.sum_union hdisj]
      calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 +
            ∑ p ∈ (Ioc (2 * y) N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ 2 * Real.log 4 * Real.log (2 * y) / y +
            4 * Real.log 4 * (Real.log ((2 * y : ℕ) : ℝ) + 2 * Real.log 2) / ((2 * y : ℕ) : ℝ) :=
            add_le_add hblock ht
        _ = 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            push_cast
            rw [hlog2y]
            field_simp
            ring

private theorem sP_cN_nonneg (y : ℝ) (hy : 0 ≤ y) (N p : ℕ) : 0 ≤ sP (cN y) N p :=
  Pairs.sP_nonneg (fun n => cN_nonneg y hy n) N p

private theorem sum_sP_sq_large_primes_le (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ 96 * Real.log 4 * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  have hY3 : 3 ≤ Y := Nat.le_floor (by exact_mod_cast hy)
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hYlt : y < (Y : ℝ) + 1 := Nat.lt_floor_add_one y
  have hY3r : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hy0 : 0 < y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hset : ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ Y) = (Ioc Y N).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨by omega, h2⟩, hp⟩, by omega⟩
  rw [hset]
  have hterm : ∀ p ∈ (Ioc Y N).filter Nat.Prime,
      sP (cN y) N p ^ 2 ≤ 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := sP_cN_le_log_div y hy0.le N p hpp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    calc sP (cN y) N p ^ 2 ≤ (2 * y * Real.log p / p) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
        field_simp
        ring
  have htail := sum_log_sq_div_sq_primes_tail_le N (N - Y) Y (by omega) le_rfl
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogY : Real.log Y ≤ Real.log y := Real.log_le_log hY0 hYle
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
  have hq : 4 * Real.log 4 * (Real.log Y + 2 * Real.log 2) / Y ≤ 24 * Real.log 4 * Real.log y / y := by
    rw [div_le_div_iff₀ hY0 hy0]
    have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hE : Real.log Y + 2 * Real.log 2 ≤ 3 * Real.log y := by linarith
    have h1 : (Real.log Y + 2 * Real.log 2) * y ≤ 3 * Real.log y * y :=
      mul_le_mul_of_nonneg_right hE hy0.le
    have h2 : 3 * Real.log y * y ≤ 3 * Real.log y * (2 * Y) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ 4 * Real.log 4 by positivity)
    linarith only [h3]
  calc ∑ p ∈ (Ioc Y N).filter Nat.Prime, sP (cN y) N p ^ 2
      ≤ ∑ p ∈ (Ioc Y N).filter Nat.Prime, 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := sum_le_sum hterm
    _ = 4 * y ^ 2 * ∑ p ∈ (Ioc Y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 4 * y ^ 2 * (24 * Real.log 4 * Real.log y / y) :=
        mul_le_mul_of_nonneg_left (htail.trans hq) (by positivity)
    _ = 96 * Real.log 4 * (y * Real.log y) := by
        field_simp
        ring

private theorem sum_sP_sq_small_primes_le_of_bound (C0 : ℝ) (hC0 : 0 < C0)
    (hb : ∀ (y : ℝ), 3 ≤ y → ∀ (N p : ℕ), sP (cN y) N p ≤ C0 * Real.log y) (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ (4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4) * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  set S := ⌊Real.sqrt y⌋₊ with hSdef
  have hy0 : 0 < y := by linarith
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hsq0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hSle : (S : ℝ) ≤ Real.sqrt y := Nat.floor_le hsq0
  have hSlt : Real.sqrt y < (S : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsqsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hsq1 : 1 ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogsq : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0.le
  have hlsy : Real.log y ≤ 2 * Real.sqrt y := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt y by linarith)
    rw [hlogsq] at this
    linarith
  have hsub : ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ Y) ⊆ (range (Y + 1)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Icc, mem_range] at hp ⊢
    exact ⟨by omega, hp.1.2⟩
  have step1 := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => sP (cN y) N p ^ 2) (fun p _ _ => sq_nonneg _)
  have hterm : ∀ p ∈ (range (Y + 1)).filter Nat.Prime, sP (cN y) N p ^ 2 ≤
      (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0) + 2 * C0 ^ 2 * Real.log y * Real.log p := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := hb y hy N p
    have hsqb : sP (cN y) N p ^ 2 ≤ C0 ^ 2 * Real.log y ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ h0 h1 2
    have hx : 0 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by positivity
    split_ifs with hpS
    · linarith only [hsqb, hx]
    · have hpS' : (S : ℝ) + 1 ≤ p := by exact_mod_cast (show S + 1 ≤ p by omega)
      have hlt : Real.sqrt y < p := by linarith
      have hlog : Real.log (Real.sqrt y) ≤ Real.log p := Real.log_le_log (by linarith) hlt.le
      rw [hlogsq] at hlog
      have hprod : C0 ^ 2 * Real.log y ^ 2 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by
        have hc : 0 ≤ C0 ^ 2 * Real.log y := by positivity
        have h := mul_le_mul_of_nonneg_left (show Real.log y ≤ 2 * Real.log p by linarith only [hlog]) hc
        linarith only [h]
      linarith only [hsqb, hprod]
  have step2 := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at step2
  have hite : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0)
      ≤ ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
    rw [← sum_filter]
    have hsub2 : ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S) ⊆ range (S + 1) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp ⊢
      omega
    calc ∑ p ∈ ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S), C0 ^ 2 * Real.log y ^ 2
        ≤ ∑ p ∈ range (S + 1), C0 ^ 2 * Real.log y ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => by positivity)
      _ = ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
  have htheta := sum_log_primes_le_mul_log_four Y
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hA : ((S : ℝ) + 1) * Real.log y ≤ 4 * y := by
    have hprod : ((S : ℝ) + 1) * Real.log y ≤ (Real.sqrt y + 1) * (2 * Real.sqrt y) :=
      mul_le_mul (by linarith only [hSle]) hlsy hly (by linarith only [hsq0])
    have hsqle := le_mul_of_one_le_right hsq0 hsq1
    linarith only [hprod, hsqle, hsqsq]
  have hA' : ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) ≤ 4 * C0 ^ 2 * (y * Real.log y) := by
    have h := mul_le_mul_of_nonneg_right hA (show 0 ≤ C0 ^ 2 * Real.log y by positivity)
    linarith only [h]
  have hB : 2 * C0 ^ 2 * Real.log y * ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p
      ≤ 2 * C0 ^ 2 * Real.log 4 * (y * Real.log y) := by
    have h1 : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ y * Real.log 4 :=
      htheta.trans (mul_le_mul_of_nonneg_right hYle hL.le)
    have h := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C0 ^ 2 * Real.log y by positivity)
    linarith only [h]
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := by linarith only [hite, hA', hB]

/-- Summing over the prime bases preserves the bound `O(y log y)`. -/
theorem sPsq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N : ℕ,
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN y) N p ^ 2 ≤ C * y * Real.log y := by
  obtain ⟨C0, hC0, hb⟩ := exists_primePowerSum_le_mul_log
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4 + 96 * Real.log 4, by positivity, ?_⟩
  intro y hy N
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => p ≤ ⌊y⌋₊)]
  have h3 := sum_sP_sq_small_primes_le_of_bound C0 hC0 hb y hy N
  have h2 := sum_sP_sq_large_primes_le y hy N
  linarith only [h3, h2]

end QH
