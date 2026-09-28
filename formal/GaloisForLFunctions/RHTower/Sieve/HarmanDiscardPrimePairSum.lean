import GaloisForLFunctions.RHTower.Sieve.MertensRiemannEnvelopes
import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardPrimeDensity

/-!
# The prime-cofactor discarded sum over prime pairs

`∑_{q₂} (1/q₂) ∑_{q₁} 1/(q₁ (1 - α₁ - α₂))` over the discarded region (`αᵢ = log qᵢ/log y`) is
eventually at most `0.8896 + η`: the inner sum is the section `harmanDiscardPrimeInner` up to `η`
(uniform Mertens–Riemann), and the outer sum is bounded cellwise by the envelopes of
`HarmanDiscardPrimeDensity`.
-/

namespace RHTower.Sieve

open Real Filter Topology Finset

noncomputable section

/-- The logarithmic scale `log p / log y` of a prime in `(y^c, y^d]` lies in `(c, d]`. -/
theorem logScale_mem_of_mem_Ioc_floor {y c d : ℝ} {p : ℕ} (hy : 1 < y)
    (hp : p ∈ Finset.Ioc ⌊y ^ c⌋₊ ⌊y ^ d⌋₊) : c < log p / log y ∧ log p / log y ≤ d := by
  have hly : 0 < log y := Real.log_pos hy
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hp
  have hp0 : (0 : ℝ) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  constructor
  · rw [lt_div_iff₀ hly]
    have hlt : y ^ c < p := by
      have := Nat.lt_floor_add_one (y ^ c)
      have h' : ((⌊y ^ c⌋₊ : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast h1
      linarith
    have := Real.log_lt_log (by positivity) hlt
    rw [Real.log_rpow (by linarith)] at this
    linarith
  · rw [div_le_iff₀ hly]
    have hle : (p : ℝ) ≤ y ^ d := by
      have hd : (0 : ℝ) < y ^ d := by positivity
      have : (⌊y ^ d⌋₊ : ℝ) ≤ y ^ d := Nat.floor_le hd.le
      have h2' : (p : ℝ) ≤ ⌊y ^ d⌋₊ := by exact_mod_cast h2
      linarith
    have := Real.log_le_log hp0 hle
    rwa [Real.log_rpow (by linarith)] at this

/-- The inner prime sum of the prime-cofactor term. -/
def harmanPrimeInnerSum (y κ α₂ : ℝ) : ℝ :=
  primeScaleSum y (harmanDiscardLow κ α₂) (harmanDiscardHigh κ α₂) (fun α₁ => 1 / (1 - α₁ - α₂))

/-- The inner prime sum is the section up to `η`, uniformly in `α₂ ∈ [2/11, (1+κ)/3]`. -/
theorem eventually_abs_harmanPrimeInnerSum_sub_le {κ η : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1 / 1000)
    (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, ∀ α₂ ∈ Set.Icc (2 / 11 : ℝ) ((1 + κ) / 3),
      |harmanPrimeInnerSum y κ α₂ - harmanDiscardPrimeInner κ α₂| ≤ η := by
  filter_upwards [eventually_abs_primeScaleSum_sub_integral_le (a₀ := 1 / 6) (b₀ := 1) (M := 6)
    (L := 36) (by norm_num) hη (by norm_num)] with y hy
  intro α₂ hα
  have hlo : α₂ ≤ harmanDiscardLow κ α₂ := le_max_left _ _
  have hhi : harmanDiscardHigh κ α₂ ≤ 1 + κ - 2 * α₂ := min_le_right _ _
  have hlh := harmanDiscardLow_le_high hκ hα.2
  have hden : ∀ x ∈ Set.Icc (harmanDiscardLow κ α₂) (harmanDiscardHigh κ α₂),
      1 / 6 ≤ (1 - α₂) + (-1) * x := by
    intro x hx; linarith [hx.2, hα.1]
  have hLip := lipschitzBound_inv_affine (p := 1 - α₂) (q := -1) (m := 1 / 6) (by norm_num) hden
  have hform : (fun x => 1 / ((1 - α₂) + (-1) * x)) = fun α₁ => 1 / (1 - α₁ - α₂) := by
    funext x; congr 1; ring
  rw [hform] at hLip
  have hM : ∀ x ∈ Set.Icc (harmanDiscardLow κ α₂) (harmanDiscardHigh κ α₂),
      |1 / (1 - x - α₂)| ≤ 6 := by
    intro x hx
    have h6 : 1 / 6 ≤ 1 - x - α₂ := by have := hden x hx; linarith
    rw [abs_of_pos (by positivity)]
    calc 1 / (1 - x - α₂) ≤ 1 / (1 / 6) := one_div_le_one_div_of_le (by norm_num) h6
      _ = 6 := by norm_num
  have h := hy _ _ (by linarith [hα.1]) hlh (by linarith [hα.1]) _ hM
    (hLip.mono_const (by norm_num))
  unfold harmanPrimeInnerSum harmanDiscardPrimeInner
  have e : (∫ α₁ in harmanDiscardLow κ α₂..harmanDiscardHigh κ α₂, 1 / (1 - α₁ - α₂) / α₁)
      = ∫ α₁ in harmanDiscardLow κ α₂..harmanDiscardHigh κ α₂, 1 / (α₁ * (1 - α₁ - α₂)) := by
    congr 1; funext x; rw [div_div, mul_comm]
  rw [← e]
  exact h

/-- One cell of the outer sum: primes `q₂ ∈ (y^c, y^d]` against an envelope `P` of the section. -/
theorem sum_cell_harmanPrimeInnerSum_le {y κ c d η₁ : ℝ} {P : ℝ → ℝ} (hy : 1 < y)
    (hc : 2 / 11 ≤ c) (hd : d ≤ (1 + κ) / 3)
    (hin : ∀ α₂ ∈ Set.Icc (2 / 11 : ℝ) ((1 + κ) / 3),
      |harmanPrimeInnerSum y κ α₂ - harmanDiscardPrimeInner κ α₂| ≤ η₁)
    (hcell : ∀ x ∈ Set.Icc c d, harmanDiscardPrimeInner κ x ≤ P x) :
    ∑ p ∈ (Finset.Ioc ⌊y ^ c⌋₊ ⌊y ^ d⌋₊).filter Nat.Prime,
        1 / (p : ℝ) * harmanPrimeInnerSum y κ (log p / log y)
      ≤ primeScaleSum y c d P
        + η₁ * ∑ p ∈ (Finset.Ioc ⌊y ^ c⌋₊ ⌊y ^ d⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
  unfold primeScaleSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun p hp => ?_)
  have hp0 : (0 : ℝ) < p := by
    have := (Finset.mem_filter.1 hp).2.pos; exact_mod_cast this
  obtain ⟨h1, h2⟩ := logScale_mem_of_mem_Ioc_floor hy (Finset.mem_filter.1 hp).1
  have hmem : log p / log y ∈ Set.Icc c d := ⟨h1.le, h2⟩
  have hmem' : log p / log y ∈ Set.Icc (2 / 11 : ℝ) ((1 + κ) / 3) :=
    ⟨hc.trans h1.le, h2.trans hd⟩
  have hi := (abs_le.mp (hin _ hmem')).2
  have hP := hcell _ hmem
  have hq : 0 ≤ 1 / (p : ℝ) := by positivity
  calc 1 / (p : ℝ) * harmanPrimeInnerSum y κ (log p / log y)
      ≤ 1 / (p : ℝ) * (P (log p / log y) + η₁) :=
        mul_le_mul_of_nonneg_left (by linarith) hq
    _ = P (log p / log y) / p + η₁ * (1 / p) := by ring

/-- **The prime-cofactor discarded sum over prime pairs** is eventually at most `0.8896 + η`. -/
theorem eventually_harmanPrimePairSum_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ y : ℝ in atTop, ∑ p ∈ (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 3 : ℝ)⌋₊).filter Nat.Prime,
        1 / (p : ℝ) * harmanPrimeInnerSum y (1 / 1000000) (log p / log y) ≤ 8896 / 10000 + η := by
  have hη4 : 0 < η / 4 := by positivity
  have hc : 0 < η / 52 := by positivity
  filter_upwards [eventually_abs_harmanPrimeInnerSum_sub_le (κ := 1 / 1000000) (by norm_num)
      (by norm_num) hη4,
    eventually_sum_prime_inv_rpow_le (a := 2 / 11) (b := (1 + 1 / 1000000) / 3) (η := 1) (by norm_num)
      (by norm_num) one_pos,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 2 / 11) (b := 3 / 16)
      (P := harmanDiscardPrimeCellEnvelope0) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope0,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 3 / 16) (b := (1 - 1 / 1000000) / 5)
      (P := harmanDiscardPrimeCellEnvelope1) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope1,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := (1 - 1 / 1000000) / 5) (b := 17 / 80)
      (P := harmanDiscardPrimeCellEnvelope2) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope2,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 17 / 80) (b := 9 / 40)
      (P := harmanDiscardPrimeCellEnvelope3) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope3,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 9 / 40) (b := 19 / 80)
      (P := harmanDiscardPrimeCellEnvelope4) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope4,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 19 / 80) (b := 1 / 4)
      (P := harmanDiscardPrimeCellEnvelope5) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope5,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 1 / 4) (b := 21 / 80)
      (P := harmanDiscardPrimeCellEnvelope6) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope6,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 21 / 80) (b := 11 / 40)
      (P := harmanDiscardPrimeCellEnvelope7) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope7,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 11 / 40) (b := 23 / 80)
      (P := harmanDiscardPrimeCellEnvelope8) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope8,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 23 / 80) (b := 3 / 10)
      (P := harmanDiscardPrimeCellEnvelope9) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope9,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 3 / 10) (b := 5 / 16)
      (P := harmanDiscardPrimeCellEnvelope10) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope10,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 5 / 16) (b := 13 / 40)
      (P := harmanDiscardPrimeCellEnvelope11) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope11,
    eventually_primeScaleSum_le_of_affine_div_one_sub (a := 13 / 40) (b := (1 + 1 / 1000000) / 3)
      (P := harmanDiscardPrimeCellEnvelope12) (by norm_num) (by norm_num) (by norm_num) hc
      ⟨_, _, fun x => rfl⟩ integral_harmanDiscardPrimeCellEnvelope12,
    eventually_gt_atTop (1 : ℝ)] with y hin hmert h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hy1
  have hmono : ∀ c d : ℝ, c ≤ d → ⌊y ^ c⌋₊ ≤ ⌊y ^ d⌋₊ := fun c d h =>
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hy1.le h)
  have split : ∀ f : ℕ → ℝ,
      ∑ p ∈ (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 3 : ℝ)⌋₊).filter Nat.Prime, f p =
        (∑ p ∈ (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ (3 / 16 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (3 / 16 : ℝ)⌋₊ ⌊y ^ ((1 - 1 / 1000000) / 5 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ ((1 - 1 / 1000000) / 5 : ℝ)⌋₊ ⌊y ^ (17 / 80 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (17 / 80 : ℝ)⌋₊ ⌊y ^ (9 / 40 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (9 / 40 : ℝ)⌋₊ ⌊y ^ (19 / 80 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (19 / 80 : ℝ)⌋₊ ⌊y ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (1 / 4 : ℝ)⌋₊ ⌊y ^ (21 / 80 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (21 / 80 : ℝ)⌋₊ ⌊y ^ (11 / 40 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (11 / 40 : ℝ)⌋₊ ⌊y ^ (23 / 80 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (23 / 80 : ℝ)⌋₊ ⌊y ^ (3 / 10 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (3 / 10 : ℝ)⌋₊ ⌊y ^ (5 / 16 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (5 / 16 : ℝ)⌋₊ ⌊y ^ (13 / 40 : ℝ)⌋₊).filter Nat.Prime, f p)
        + (∑ p ∈ (Finset.Ioc ⌊y ^ (13 / 40 : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 3 : ℝ)⌋₊).filter Nat.Prime, f p) := by
    intro f
    simp only [Finset.sum_filter]
    rw [← Finset.sum_Ioc_consecutive _ (hmono (2 / 11) (3 / 16) (by norm_num))
        (hmono (3 / 16) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (3 / 16) ((1 - 1 / 1000000) / 5) (by norm_num))
        (hmono ((1 - 1 / 1000000) / 5) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono ((1 - 1 / 1000000) / 5) (17 / 80) (by norm_num))
        (hmono (17 / 80) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (17 / 80) (9 / 40) (by norm_num))
        (hmono (9 / 40) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (9 / 40) (19 / 80) (by norm_num))
        (hmono (19 / 80) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (19 / 80) (1 / 4) (by norm_num))
        (hmono (1 / 4) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (1 / 4) (21 / 80) (by norm_num))
        (hmono (21 / 80) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (21 / 80) (11 / 40) (by norm_num))
        (hmono (11 / 40) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (11 / 40) (23 / 80) (by norm_num))
        (hmono (23 / 80) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (23 / 80) (3 / 10) (by norm_num))
        (hmono (3 / 10) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (3 / 10) (5 / 16) (by norm_num))
        (hmono (5 / 16) ((1 + 1 / 1000000) / 3) (by norm_num)),
      ← Finset.sum_Ioc_consecutive _ (hmono (5 / 16) (13 / 40) (by norm_num))
        (hmono (13 / 40) ((1 + 1 / 1000000) / 3) (by norm_num))]
    ring
  have c0 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope0
  have c1 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope1
  have c2 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope2
  have c3 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope3
  have c4 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope4
  have c5 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope5
  have c6 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope6
  have c7 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope7
  have c8 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope8
  have c9 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope9
  have c10 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope10
  have c11 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope11
  have c12 := sum_cell_harmanPrimeInnerSum_le hy1 (by norm_num) (by norm_num) hin
    harmanDiscardPrimeInner_le_cellEnvelope12
  have hs1 := split (fun p => 1 / (p : ℝ) * harmanPrimeInnerSum y (1 / 1000000) (log p / log y))
  have hs2 := split (fun p => 1 / (p : ℝ))

  have hlog : log (((1 + 1 / 1000000) / 3) / (2 / 11)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((1 + 1 / 1000000) / 3) / (2 / 11) by norm_num)
    norm_num at this ⊢; linarith
  have hpos : 0 ≤ η / 4 := hη4.le
  have hmert' : η / 4 * ∑ p ∈ (Finset.Ioc ⌊y ^ (2 / 11 : ℝ)⌋₊ ⌊y ^ ((1 + 1 / 1000000) / 3 : ℝ)⌋₊).filter Nat.Prime,
      1 / (p : ℝ) ≤ η / 4 * 2 := mul_le_mul_of_nonneg_left (by linarith) hpos
  rw [hs1]
  rw [hs2] at hmert'
  linarith

end

end RHTower.Sieve
