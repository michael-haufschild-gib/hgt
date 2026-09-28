import GaloisForLFunctions.RHTower.Sieve.HarmanWindowPrimeCofactor
import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardTwoPrimeTripleSum

/-!
# The two-prime-cofactor part of the discarded pair tail

Over the window `(y, y(1+θ)]`, the part of the discarded pair tail `D₂` with cofactor `m = p r`,
`q₂ ≤ p ≤ r` primes, is a sum of prime counts over prime triples `(q₁, q₂, p)`.  Off the diagonal
(`p > q₂`) the triples lie in the region of `harmanDiscardTwoPrimeSection`, and the sum is at most
`(1+η)(θy/log y)(0.0960 + η)`; the diagonal `p = q₂` is `O(θy log y/(y^{2/11} log y))`.
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

noncomputable section

/-- Split off the diagonal `p = q` of a prime sum over `[q, B]`. -/
theorem sum_Icc_prime_le_diag_add {q B : ℕ} (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∑ p ∈ (Finset.Icc q B).filter Nat.Prime, f p
      ≤ f q + ∑ p ∈ (Finset.Ioc q B).filter Nat.Prime, f p := by
  have hsub : (Finset.Icc q B).filter Nat.Prime ⊆
      insert q ((Finset.Ioc q B).filter Nat.Prime) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    rcases eq_or_lt_of_le hp.1.1 with h | h
    · exact Finset.mem_insert.2 (Or.inl h.symm)
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h, hp.1.2⟩, hp.2⟩)
  calc ∑ p ∈ (Finset.Icc q B).filter Nat.Prime, f p
      ≤ ∑ p ∈ insert q ((Finset.Ioc q B).filter Nat.Prime), f p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf p)
    _ = f q + ∑ p ∈ (Finset.Ioc q B).filter Nat.Prime, f p := by
        rw [Finset.sum_insert (by simp)]

/-- Logarithmic coordinates of a discarded pair with a second cofactor prime `p > q₂`. -/
theorem harmanDiscardTriple_mem {κ y θ : ℝ} {z Q D E q₁ q₂ p : ℕ} (hy : 1 < y) (hθ1 : θ ≤ 1)
    (hyκ : 2 ≤ y ^ κ) (hP : HarmanWindowScale κ y z Q D E)
    (hq : (q₁, q₂) ∈ harmanDiscardPairSet z Q D E) (hp : p.Prime) (h2p : q₂ < p)
    (hdr : (q₁ : ℝ) * q₂ * p * p ≤ y * (1 + θ)) :
    q₂ ∈ (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + κ) / 4 : ℝ)⌋₊).filter Nat.Prime ∧
      q₁ ∈ (Finset.Ioc ⌊y ^ harmanDiscardLow κ (log q₂ / log y)⌋₊
        ⌊y ^ harmanDiscardHighTwo κ (log q₂ / log y)⌋₊).filter Nat.Prime ∧
      p ∈ (Finset.Ioc ⌊y ^ (log q₂ / log y)⌋₊
        ⌊y ^ ((1 + κ - log q₁ / log y - log q₂ / log y) / 2)⌋₊).filter Nat.Prime := by
  have hmem := hq
  simp only [harmanDiscardPairSet, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Ico] at hq
  have hp1 := hq.2.1
  have hp2 := hq.2.2.1
  have hly : 0 < log y := Real.log_pos hy
  have hy0 : 0 < y := by linarith
  have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
  have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h2p' : (q₂ : ℝ) < p := by exact_mod_cast h2p
  have hdr2 : ((q₁ * q₂ : ℕ) : ℝ) * q₂ ≤ y * (1 + θ) := by
    push_cast
    have : (q₁ : ℝ) * q₂ * q₂ ≤ q₁ * q₂ * p * p := by
      have h1 : (q₂ : ℝ) ≤ p * p := by nlinarith [(by exact_mod_cast hp.one_lt.le : (1 : ℝ) ≤ p)]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ q₁ * q₂)
      linarith
    linarith
  obtain ⟨hα2, h21, hα1Q, _, hdisc⟩ := harmanDiscardPair_logScale hy hθ1 hyκ hP hmem hdr2
  have h23 : log q₂ / log y < log p / log y := div_lt_div_of_pos_right (Real.log_lt_log hq2 h2p') hly
  have hsum : log q₁ / log y + log q₂ / log y + 2 * (log p / log y) ≤ 1 + κ := by
    have h2y : y * (1 + θ) ≤ y ^ (1 + κ) := by
      rw [Real.rpow_add hy0, Real.rpow_one]; nlinarith
    have := logScale_le_of_le_rpow hy (by positivity) (hdr.trans h2y)
    rw [Real.log_mul (by positivity) hpp.ne', Real.log_mul (by positivity) hpp.ne',
      Real.log_mul hq1.ne' hq2.ne'] at this
    have e : (log q₁ + log q₂ + log p + log p) / log y
        = log q₁ / log y + log q₂ / log y + 2 * (log p / log y) := by ring
    linarith
  refine ⟨Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy hp2.pos).2 ⟨hα2, by linarith⟩, hp2⟩,
    Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy hp1.pos).2 ⟨?_, ?_⟩, hp1⟩,
    Finset.mem_filter.2 ⟨(mem_Ioc_floor_rpow_iff hy hp.pos).2 ⟨h23, by linarith⟩, hp⟩⟩
  · refine max_lt h21 ?_
    rcases hdisc with h | h
    · exact lt_of_le_of_lt (min_le_left _ _) h
    · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · exact le_min hα1Q (by linarith)

/-- **The two-prime-cofactor part, off the diagonal.** -/
theorem eventually_sum_harmanDiscardPair_twoPrime_le {c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hB2 : ∀ᶠ Z : ℝ in atTop, ∀ θ : ℝ, exp (-c * sqrt (log Z)) ≤ θ → θ ≤ 1 →
      ((primesIn Z (Z * (1 + θ))).card : ℝ) ≤ (1 + η) * (θ * Z / log Z)) :
    ∀ᶠ y : ℝ in atTop, ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ z Q D E : ℕ, HarmanWindowScale (1 / 1000000) y z Q D E →
      ∑ qq ∈ harmanDiscardPairSet z Q D E,
        ∑ p ∈ (Finset.Ioc qq.2 (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2))).filter Nat.Prime,
          (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / p) (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / p) p : ℝ)
        ≤ (1 + η) * (θ * y / log y) * (960 / 10000 + η) := by
  filter_upwards [eventually_primeCountAbove_window_le hc hB2,
    eventually_harmanTwoPrimeTripleSum_le hη,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000000)).eventually_ge_atTop 2,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 11)).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with y hwin hsum hyκ hy211 hy1
  intro θ hθ hθ1 z Q D E hP
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθ
  have hly : 0 < log y := Real.log_pos hy1
  have hy0 : 0 < y := by linarith
  set κ : ℝ := 1 / 1000000 with hκ
  set C := (1 + η) * (θ * y / log y) with hC
  have hC0 : 0 ≤ C := by positivity
  set S₂ := (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + κ) / 4 : ℝ)⌋₊).filter Nat.Prime with hS₂
  set S₁ : ℕ → Finset ℕ := fun q₂ => (Finset.Ioc ⌊y ^ harmanDiscardLow κ (log q₂ / log y)⌋₊
    ⌊y ^ harmanDiscardHighTwo κ (log q₂ / log y)⌋₊).filter Nat.Prime with hS₁
  set S₃ : ℕ → ℕ → Finset ℕ := fun q₁ q₂ => (Finset.Ioc ⌊y ^ (log q₂ / log y)⌋₊
    ⌊y ^ ((1 + κ - log q₁ / log y - log q₂ / log y) / 2)⌋₊).filter Nat.Prime with hS₃
  set G₃ : ℕ → ℕ → ℕ → ℝ := fun q₁ q₂ p => C * (1 / (q₂ : ℝ) * (1 / (q₁ : ℝ) *
    ((1 / (1 - log q₁ / log y - log q₂ / log y - log p / log y)) / p))) with hG₃
  -- nonnegativity on the region
  have hG₃0 : ∀ q₁ q₂ p, q₂ ∈ S₂ → q₁ ∈ S₁ q₂ → p ∈ S₃ q₁ q₂ → 0 ≤ G₃ q₁ q₂ p := by
    intro q₁ q₂ p h2 h1 h3
    have hp2 := (Finset.mem_filter.1 h2).2
    have hp1 := (Finset.mem_filter.1 h1).2
    have hp := (Finset.mem_filter.1 h3).2
    have a2 := (mem_Ioc_floor_rpow_iff hy1 hp2.pos).1 (Finset.mem_filter.1 h2).1
    have a1 := (mem_Ioc_floor_rpow_iff hy1 hp1.pos).1 (Finset.mem_filter.1 h1).1
    have a3 := (mem_Ioc_floor_rpow_iff hy1 hp.pos).1 (Finset.mem_filter.1 h3).1
    have hhi : harmanDiscardHighTwo κ (log q₂ / log y) ≤ 1 + κ - 3 * (log q₂ / log y) :=
      min_le_right _ _
    have hpos : 0 < 1 - log q₁ / log y - log q₂ / log y - log p / log y := by
      simp only [hκ] at a1 a2 a3 hhi ⊢; linarith [a1.2, a2.1, a3.2]
    have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
    have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
    have hpp : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp only [hG₃]
    positivity
  have key : ∑ qq ∈ harmanDiscardPairSet z Q D E,
      ∑ p ∈ (Finset.Ioc qq.2 (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2))).filter Nat.Prime,
        (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / p) (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / p) p : ℝ)
      ≤ ∑ q₂ ∈ S₂, ∑ q₁ ∈ S₁ q₂, ∑ p ∈ S₃ q₁ q₂, G₃ q₁ q₂ p := by
    refine sum_pairs_le_nested (G := fun t : ℕ × ℕ => ∑ p ∈ S₃ t.1 t.2, G₃ t.1 t.2 p)
      (fun q₂ h2 q₁ h1 => Finset.sum_nonneg
      (fun p h3 => hG₃0 q₁ q₂ p h2 h1 h3)) (fun t ht => ?_)
    obtain ⟨q₁, q₂⟩ := t
    have hmem := ht
    simp only [harmanDiscardPairSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ico] at ht
    have hp1 := ht.2.1
    have hp2 := ht.2.2.1
    have hd : 0 < q₁ * q₂ := Nat.mul_pos hp1.pos hp2.pos
    -- a nonzero count at `p` places the triple in the region
    have hreg_of : ∀ p ∈ (Finset.Ioc q₂ (⌊y * (1 + θ)⌋₊ / (q₁ * q₂))).filter Nat.Prime,
        primeCountAbove (⌊y⌋₊ / (q₁ * q₂) / p) (⌊y * (1 + θ)⌋₊ / (q₁ * q₂) / p) p ≠ 0 →
        (q₂ ∈ S₂ ∧ q₁ ∈ S₁ q₂ ∧ p ∈ S₃ q₁ q₂) ∧ (q₁ : ℝ) * q₂ * p * p ≤ y * (1 + θ) := by
      intro p hp h0
      have hpP := (Finset.mem_filter.1 hp).2
      have h2p := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hp).1).1
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul] at h0
      have hdrN := mul_le_of_primeCountAbove_ne_zero (Nat.mul_pos hd hpP.pos) h0
      have hbr : (⌊y * (1 + θ)⌋₊ : ℝ) ≤ y * (1 + θ) := Nat.floor_le (by positivity)
      have hdr : (q₁ : ℝ) * q₂ * p * p ≤ y * (1 + θ) := by
        have : ((q₁ * q₂ * p * p : ℕ) : ℝ) ≤ ⌊y * (1 + θ)⌋₊ := by exact_mod_cast hdrN
        push_cast at this; linarith
      exact ⟨harmanDiscardTriple_mem hy1 hθ1 hyκ hP hmem hpP h2p hdr, hdr⟩
    by_cases hreg : q₂ ∈ S₂ ∧ q₁ ∈ S₁ q₂
    · rw [if_pos hreg]
      simp only
      refine sum_le_sum_of_le_ite (fun p h3 => hG₃0 q₁ q₂ p hreg.1 hreg.2 h3) (fun p hp => ?_)
      by_cases h0 : primeCountAbove (⌊y⌋₊ / (q₁ * q₂) / p)
          (⌊y * (1 + θ)⌋₊ / (q₁ * q₂) / p) p = 0
      · rw [h0, Nat.cast_zero]
        split_ifs with h3
        · exact hG₃0 q₁ q₂ p hreg.1 hreg.2 h3
        · exact le_rfl
      obtain ⟨⟨_, _, h3⟩, hdr⟩ := hreg_of p hp h0
      rw [if_pos h3]
      have hpP := (Finset.mem_filter.1 hp).2
      have h2p := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hp).1).1
      have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
      have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
      have hpp : (0 : ℝ) < p := by exact_mod_cast hpP.pos
      have hdp : 0 < q₁ * q₂ * p := Nat.mul_pos hd hpP.pos
      have h6 : y ^ (1 / 6 : ℝ) ≤ (p : ℝ) := by
        have h611 : y ^ (1 / 6 : ℝ) ≤ y ^ (2 / 11 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num)
        have : (z : ℝ) ≤ q₂ := by exact_mod_cast ht.1.2.1
        have : (q₂ : ℝ) < p := by exact_mod_cast h2p
        linarith [hP.z_gt]
      have hdr' : ((q₁ * q₂ * p : ℕ) : ℝ) * p ≤ y * (1 + θ) := by push_cast; linarith
      have hcount := hwin θ hθ hθ1 (q₁ * q₂ * p) p hdp h6 hdr'
      have hdy : ((q₁ * q₂ * p : ℕ) : ℝ) < y := by
        have h2 : (2 : ℝ) < p := by
          have : (z : ℝ) ≤ q₂ := by exact_mod_cast ht.1.2.1
          have : (q₂ : ℝ) < p := by exact_mod_cast h2p
          linarith [hP.z_gt, hy211]
        have hd0 : (0 : ℝ) < ((q₁ * q₂ * p : ℕ) : ℝ) := by exact_mod_cast hdp
        have : ((q₁ * q₂ * p : ℕ) : ℝ) * 2 < y * (1 + θ) :=
          lt_of_lt_of_le (mul_lt_mul_of_pos_left h2 hd0) hdr'
        nlinarith
      rw [div_log_div_eq hy1 hdp hdy] at hcount
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      refine hcount.trans (le_of_eq ?_)
      simp only [hG₃, hC]
      rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) hpp.ne',
        Real.log_mul hq1.ne' hq2.ne']
      ring
    · rw [if_neg hreg]
      refine Finset.sum_nonpos (fun p hp => ?_)
      by_cases h0 : primeCountAbove (⌊y⌋₊ / (q₁ * q₂) / p)
          (⌊y * (1 + θ)⌋₊ / (q₁ * q₂) / p) p = 0
      · rw [h0, Nat.cast_zero]
      · exact absurd ⟨(hreg_of p hp h0).1.1, (hreg_of p hp h0).1.2.1⟩ hreg
  refine key.trans ?_
  have hinner : ∀ q₂ ∈ S₂, ∑ q₁ ∈ S₁ q₂, ∑ p ∈ S₃ q₁ q₂, G₃ q₁ q₂ p =
      C * (1 / (q₂ : ℝ) * harmanTwoPrimeMiddleSum y κ (log q₂ / log y)) := by
    intro q₂ _
    simp only [hG₃, hS₁, hS₃, harmanTwoPrimeMiddleSum, harmanTwoPrimeInnerSum, primeScaleSum]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q₁ _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hsum hC0

/-- The window bound on the diagonal: `y/d ≥ y^{1/11}` for `d = q₁q₂²`. -/
theorem diag_window_bound {y θ η q₁ q₂ : ℝ} (hy : 1 < y) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hq1 : 0 < q₁) (hq2 : 0 < q₂) (hq2y : y ^ (1 / 11 : ℝ) * 2 ≤ q₂)
    (hdr : q₁ * q₂ * q₂ * q₂ ≤ y * 2) :
    (1 + η) * (θ * (y / (q₁ * q₂ * q₂)) / log (y / (q₁ * q₂ * q₂)))
      ≤ (1 + η) * (θ * y / log y) * 11 * (1 / q₁ * (q₂ ^ 2)⁻¹) := by
  have hy0 : 0 < y := by linarith
  have hly : 0 < log y := Real.log_pos hy
  have hd0 : 0 < q₁ * q₂ * q₂ := by positivity
  have hyd : y ^ (1 / 11 : ℝ) ≤ y / (q₁ * q₂ * q₂) := by
    rw [le_div_iff₀ hd0]
    have h0 : 0 ≤ y ^ (1 / 11 : ℝ) := Real.rpow_nonneg hy0.le _
    have : y ^ (1 / 11 : ℝ) * 2 * (q₁ * q₂ * q₂) ≤ q₂ * (q₁ * q₂ * q₂) :=
      mul_le_mul_of_nonneg_right hq2y hd0.le
    nlinarith
  have hlog : log y / 11 ≤ log (y / (q₁ * q₂ * q₂)) := by
    have := Real.log_le_log (by positivity) hyd
    rw [Real.log_rpow hy0] at this; linarith
  have hl11 : 0 < log y / 11 := div_pos hly (by norm_num)
  have hstep : θ * (y / (q₁ * q₂ * q₂)) / log (y / (q₁ * q₂ * q₂))
      ≤ θ * (y / (q₁ * q₂ * q₂)) / (log y / 11) :=
    div_le_div_of_nonneg_left (by positivity) hl11 hlog
  calc (1 + η) * (θ * (y / (q₁ * q₂ * q₂)) / log (y / (q₁ * q₂ * q₂)))
      ≤ (1 + η) * (θ * (y / (q₁ * q₂ * q₂)) / (log y / 11)) :=
        mul_le_mul_of_nonneg_left hstep (by linarith)
    _ = (1 + η) * (θ * y / log y) * 11 * (1 / q₁ * (q₂ ^ 2)⁻¹) := by
        field_simp

/-- **The two-prime-cofactor part, diagonal `p = q₂`**: at most `(1+η)(θy/log y) η`. -/
theorem eventually_sum_harmanDiscardPair_twoPrime_diag_le {c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (hB2 : ∀ᶠ Z : ℝ in atTop, ∀ θ : ℝ, exp (-c * sqrt (log Z)) ≤ θ → θ ≤ 1 →
      ((primesIn Z (Z * (1 + θ))).card : ℝ) ≤ (1 + η) * (θ * Z / log Z)) :
    ∀ᶠ y : ℝ in atTop, ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ z Q D E : ℕ, HarmanWindowScale (1 / 1000000) y z Q D E →
      ∑ qq ∈ harmanDiscardPairSet z Q D E,
          (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / qq.2)
            (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / qq.2) qq.2 : ℝ)
        ≤ (1 + η) * (θ * y / log y) * η := by
  filter_upwards [eventually_primeCountAbove_window_le hc hB2,
    eventually_sum_prime_inv_rpow_le (a := 2 / 11) (b := 1 / 2 + 1 / 1000000) (by norm_num)
      (by norm_num) one_pos,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 11)).eventually_ge_atTop (66 / η),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)).eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with y hwin hmert hy66 hy11 hy1
  intro θ hθ hθ1 z Q D E hP
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.exp_pos _) hθ
  have hly : 0 < log y := Real.log_pos hy1
  have hy0 : 0 < y := by linarith
  set κ : ℝ := 1 / 1000000 with hκ
  set C := (1 + η) * (θ * y / log y) with hC
  have hC0 : 0 ≤ C := by positivity
  have hy211 : y ^ (2 / 11 : ℝ) = y ^ (1 / 11 : ℝ) * y ^ (1 / 11 : ℝ) := by
    rw [← Real.rpow_add hy0]; norm_num
  set S₂ := Finset.Ioo ⌊y ^ (2 / 11 : ℝ)⌋₊ (⌊y⌋₊ + 1) with hS₂
  set S₁ := (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ (1 / 2 + κ)⌋₊).filter Nat.Prime with hS₁
  set G : ℕ × ℕ → ℝ := fun t => C * 11 * (1 / (t.1 : ℝ) * ((t.2 : ℝ) ^ 2)⁻¹) with hG
  have key : ∑ qq ∈ harmanDiscardPairSet z Q D E,
      (primeCountAbove (⌊y⌋₊ / (qq.1 * qq.2) / qq.2)
        (⌊y * (1 + θ)⌋₊ / (qq.1 * qq.2) / qq.2) qq.2 : ℝ)
      ≤ ∑ q₂ ∈ S₂, ∑ q₁ ∈ S₁, G (q₁, q₂) := by
    refine sum_pairs_le_nested (S₁ := fun _ => S₁) (fun q₂ _ q₁ _ => by simp only [hG]; positivity)
      (fun t ht => ?_)
    obtain ⟨q₁, q₂⟩ := t
    simp only [harmanDiscardPairSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Ico] at ht
    obtain ⟨⟨⟨_, hQ1⟩, hz2, _⟩, hp1, hp2, h21, _⟩ := ht
    simp only
    by_cases h0 : primeCountAbove (⌊y⌋₊ / (q₁ * q₂) / q₂) (⌊y * (1 + θ)⌋₊ / (q₁ * q₂) / q₂) q₂ = 0
    · rw [h0, Nat.cast_zero]
      split_ifs
      · simp only [hG]; positivity
      · exact le_rfl
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul] at h0 ⊢
    have hd : 0 < q₁ * q₂ * q₂ := Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp2.pos
    have hdrN := mul_le_of_primeCountAbove_ne_zero hd h0
    clear h0
    have hbr : (⌊y * (1 + θ)⌋₊ : ℝ) ≤ y * (1 + θ) := Nat.floor_le (by positivity)
    have hq1 : (0 : ℝ) < q₁ := by exact_mod_cast hp1.pos
    have hq2 : (0 : ℝ) < q₂ := by exact_mod_cast hp2.pos
    have hdr : ((q₁ * q₂ * q₂ : ℕ) : ℝ) * q₂ ≤ y * (1 + θ) := by
      have : ((q₁ * q₂ * q₂ * q₂ : ℕ) : ℝ) ≤ ⌊y * (1 + θ)⌋₊ := by exact_mod_cast hdrN
      push_cast at this ⊢; linarith
    have hzq : y ^ (2 / 11 : ℝ) < q₂ :=
      lt_of_lt_of_le hP.z_gt (by exact_mod_cast hz2)
    have hq1Q : (q₁ : ℝ) ≤ y ^ (1 / 2 + κ) :=
      (by exact_mod_cast hQ1.le : (q₁ : ℝ) ≤ Q).trans hP.Q_le
    have h21' : (q₂ : ℝ) < q₁ := by exact_mod_cast h21
    have hreg : q₂ ∈ S₂ ∧ q₁ ∈ S₁ := by
      refine ⟨Finset.mem_Ioo.2 ⟨(Nat.floor_lt (by positivity)).2 hzq, ?_⟩,
        Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨(Nat.floor_lt (by positivity)).2 (by linarith),
          (Nat.le_floor_iff (by positivity)).2 hq1Q⟩, hp1⟩⟩
      have h2 : (2 : ℝ) ≤ q₂ := by exact_mod_cast hp2.two_le
      have h2' : (2 : ℝ) ≤ q₁ := by exact_mod_cast hp1.two_le
      have hqy : (q₂ : ℝ) ≤ y := by
        push_cast at hdr
        have : (q₂ : ℝ) * 8 ≤ q₁ * q₂ * q₂ * q₂ := by
          have h4 : (4 : ℝ) ≤ q₁ * q₂ := by nlinarith
          have h8 : (8 : ℝ) ≤ q₁ * q₂ * q₂ := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right h8 hq2.le]
        have : y * (1 + θ) ≤ 2 * y := by nlinarith
        linarith
      have : q₂ ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy0.le).2 hqy
      omega
    rw [if_pos hreg]
    have h6 : y ^ (1 / 6 : ℝ) ≤ (q₂ : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hy1.le (by norm_num)).trans hzq.le
    have hcount := hwin θ hθ hθ1 (q₁ * q₂ * q₂) q₂ hd h6 hdr
    refine hcount.trans ?_
    have hq2' : y ^ (1 / 11 : ℝ) * 2 ≤ q₂ := by
      have := hzq; rw [hy211] at this; nlinarith [Real.rpow_nonneg hy0.le (1 / 11 : ℝ)]
    have hdr' : (q₁ : ℝ) * q₂ * q₂ * q₂ ≤ y * 2 := by
      push_cast at hdr; nlinarith
    rw [Nat.cast_mul, Nat.cast_mul]
    refine (diag_window_bound hy1 hθ0.le hη.le hq1 hq2 hq2' hdr').trans_eq ?_
    simp only [hG, hC]
  refine key.trans ?_
  have hinner : ∀ q₂ ∈ S₂, ∑ q₁ ∈ S₁, G (q₁, q₂) =
      C * 11 * (∑ q₁ ∈ S₁, 1 / (q₁ : ℝ)) * ((q₂ : ℝ) ^ 2)⁻¹ := by
    intro q₂ _
    simp only [hG]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q₁ _ => ?_)
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  have hsq : ∑ q₂ ∈ S₂, ((q₂ : ℝ) ^ 2)⁻¹ ≤ 2 / y ^ (2 / 11 : ℝ) := by
    refine (sum_Ioo_inv_sq_le _ _).trans ?_
    have : y ^ (2 / 11 : ℝ) < (⌊y ^ (2 / 11 : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) this.le
  have hS1 : ∑ q₁ ∈ S₁, 1 / (q₁ : ℝ) ≤ 3 := by
    have hlog : log ((1 / 2 + 1 / 1000000) / (2 / 11) : ℝ) ≤ 2 := by
      have := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < (1 / 2 + 1 / 1000000) / (2 / 11) by norm_num)
      norm_num at this ⊢; linarith
    have := hmert; simp only [hS₁, hκ] at this ⊢; linarith
  have hS10 : 0 ≤ ∑ q₁ ∈ S₁, 1 / (q₁ : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hy66' : 66 / y ^ (2 / 11 : ℝ) ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    have h := (div_le_iff₀ hη).1 hy66
    linarith only [h]
  have hprod : (∑ q₁ ∈ S₁, 1 / (q₁ : ℝ)) * ∑ q₂ ∈ S₂, ((q₂ : ℝ) ^ 2)⁻¹
      ≤ 3 * (2 / y ^ (2 / 11 : ℝ)) :=
    mul_le_mul hS1 hsq (Finset.sum_nonneg (fun _ _ => by positivity)) (by norm_num)
  calc C * 11 * (∑ q₁ ∈ S₁, 1 / (q₁ : ℝ)) * ∑ q₂ ∈ S₂, ((q₂ : ℝ) ^ 2)⁻¹
      = C * 11 * ((∑ q₁ ∈ S₁, 1 / (q₁ : ℝ)) * ∑ q₂ ∈ S₂, ((q₂ : ℝ) ^ 2)⁻¹) := by ring
    _ ≤ C * 11 * (3 * (2 / y ^ (2 / 11 : ℝ))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = C * (66 / y ^ (2 / 11 : ℝ)) := by ring
    _ ≤ C * η := mul_le_mul_of_nonneg_left hy66' hC0

end

end RHTower.Sieve
