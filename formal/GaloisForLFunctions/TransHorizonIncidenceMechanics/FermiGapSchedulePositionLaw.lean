import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiGapScheduleQuarterWavePackets

/-!
# The position law of a one-gap Fermi schedule

For the gap at level `h + 1 ≤ L = ⌊log₂ N⌋` the bottom quarter wave (`n = h + 1` levels) and the
top quarter wave (`n = L - h` levels) give the lower bounds `((2n+1)² - 8(2n+1))/π²`, and the
two-chain inequality gives the upper bound `(1 + 2^-(m+1)) (max(2h+2m+5, 2(L-h)+7)² + 2)/π²`.
Both are `(2 max(h, L-h) + O(m))²/π²`. Consequently, if the gap sits at relative depth
`h/L → α`,

`K_{h+1}(N)/(log₂ N)² → 4 max(α, 1-α)²/π²`.

The price of one unobserved dyadic level is set by its position alone: it is the square of the
longer of the two half-observed chains it creates. It runs from `1/π²` at half depth, where the
gap is free, to `4/π²` at either end; the selected trace (gap at level one) is the edge case.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Positivity of the packet traces -/

private theorem rayGap_ge_terms (N : ℕ) (c : ℕ → ℝ) {b : ℕ} (hb : 0 < b) (h k : ℕ) (hkh : k ≠ h) :
    fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b +
        fermiNormalizedDyadicJump N c b k ^ 2 * fermiDyadicPronicWeight (k + 1) b ≤
      fermiRayGapEnergy N c b h := by
  unfold fermiRayGapEnergy fermiRayAllBoundaryEnergy
  have hs := (fermiRay_weighted_summable N c hb).2
  have h2 := hs.sum_le_tsum {h, k} (fun i _ =>
    mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _))
  rw [sum_pair (Ne.symm hkh)] at h2
  linarith

private theorem gap_pos_of_ray_one (N : ℕ) (c : ℕ → ℝ) (h : ℕ)
    (h1 : 0 < fermiRayGapEnergy N c 1 h) : 0 < fermiGapPronicEnergy N c (h + 1) := by
  obtain ⟨hQ, hQs⟩ := fermiGapPronicEnergy_eq_sum_rays N c h
  rw [hQ]
  have := hQs.le_tsum 0 (fun j _ => fermiRayGapEnergy_nonneg N c (by omega) h)
  simp only [mul_zero, zero_add] at this
  linarith

private theorem cos_quarter_bound (n : ℕ) :
    2 - 2 * Real.cos (quarterWaveAngle n) ≤ quarterWaveAngle n ^ 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := quarterWaveAngle n)
  linarith

private theorem ratio_lower {n : ℕ} (hn : 1 ≤ n) :
    ((2 * (n : ℝ) + 1) ^ 2 - 8 * (2 * (n : ℝ) + 1)) / Real.pi ^ 2 ≤
      ((2 * (n : ℝ) + 1) / 4 - 2) /
        ((2 - 2 * Real.cos (quarterWaveAngle n)) * ((2 * (n : ℝ) + 1) / 4)) ∨
      ((2 * (n : ℝ) + 1) ^ 2 - 8 * (2 * (n : ℝ) + 1)) ≤ 0 := by
  set x : ℝ := 2 * (n : ℝ) + 1
  have hx3 : (3 : ℝ) ≤ x := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [x]; linarith
  by_cases hx8 : x ≤ 8
  · right; nlinarith
  push Not at hx8
  left
  have hθ : quarterWaveAngle n = Real.pi / x := rfl
  have hlamle := cos_quarter_bound n
  have hlampos : 0 < 2 - 2 * Real.cos (quarterWaveAngle n) := mixedChainConstant_pos n
  have hπ := Real.pi_pos
  rw [hθ, div_pow] at hlamle
  rw [hθ] at hlampos ⊢
  set lam := 2 - 2 * Real.cos (Real.pi / x)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hS : 0 ≤ x / 4 - 2 := by linarith
  have key : (x ^ 2 - 8 * x) * (lam * (x / 4)) ≤ (x ^ 2 - 8 * x) * (Real.pi ^ 2 / x ^ 2 * (x / 4)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlamle (by positivity))
      (by nlinarith)
  have e : (x ^ 2 - 8 * x) * (Real.pi ^ 2 / x ^ 2 * (x / 4)) = (x / 4 - 2) * Real.pi ^ 2 := by
    field_simp; ring
  linarith

/-! ### The two lower bounds -/

/-- The bottom quarter wave on the levels `k ≤ h`. -/
def gapBottomWave (h k : ℕ) : ℝ :=
  if k ≤ h then Real.sin (((k : ℝ) + 1) * quarterWaveAngle (h + 1)) else 0

/-- The top quarter wave on the levels `h < k ≤ L`. -/
def gapTopWave (L h k : ℕ) : ℝ :=
  if h + 1 ≤ k ∧ k ≤ L then Real.sin (((L + 1 - k : ℕ) : ℝ) * quarterWaveAngle (L - h)) else 0

/-- **Bottom lower bound.** For `h < L`, `2^L ≤ N`:
`K_{h+1}(N) ≥ ((2h+3)² - 8(2h+3))/π²`. -/
theorem fermiGapInverseConstant_ge_bottom {L N h : ℕ} (hLN : 2 ^ L ≤ N) (hhL : h < L) :
    ((2 * ((h + 1 : ℕ) : ℝ) + 1) ^ 2 - 8 * (2 * ((h + 1 : ℕ) : ℝ) + 1)) / Real.pi ^ 2 ≤
      fermiGapInverseConstant N (h + 1) := by
  set y := gapBottomWave h
  set θ := quarterWaveAngle (h + 1)
  have hy : ∀ k ≤ L, y k ^ 2 ≤ 1 := fun k _ => by
    simp only [y, gapBottomWave]; split_ifs
    · exact Real.sin_sq_le_one _
    · norm_num
  -- mass and energy
  have hS : (∑ k ∈ range (L + 1), y k ^ 2) = (2 * ((h + 1 : ℕ) : ℝ) + 1) / 4 := by
    rw [← quarterWave_mass (n := h + 1) (by omega)]
    have hsplit := sum_range_add (fun k => y k ^ 2) (h + 1) (L - h)
    rw [show h + 1 + (L - h) = L + 1 by omega] at hsplit
    rw [hsplit]
    have hz : (∑ k ∈ range (L - h), y (h + 1 + k) ^ 2) = 0 :=
      sum_eq_zero fun k _ => by simp [y, gapBottomWave, show ¬ h + 1 + k ≤ h by omega]
    rw [hz, add_zero]
    exact sum_congr rfl fun k hk => by
      have := mem_range.mp hk; simp [y, gapBottomWave, show k ≤ h by omega]
  set lam := 2 - 2 * Real.cos θ
  have hyL : y L = 0 := by simp [y, gapBottomWave, show ¬ L ≤ h by omega]
  have herase : (∑ k ∈ (range L).erase h, (y k - y (k + 1)) ^ 2) =
      ∑ k ∈ range h, (y k - y (k + 1)) ^ 2 := by
    have hsub : range h ⊆ (range L).erase h := fun k hk => by
      have := mem_range.mp hk
      exact mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩
    rw [← sum_subset hsub]
    intro k hk hkn
    have hk2 : k ≠ h := ne_of_mem_erase hk
    have hk3 : h < k := by have := mem_range.not.mp hkn; omega
    simp [y, gapBottomWave, show ¬ k ≤ h by omega, show ¬ k + 1 ≤ h by omega]
  have hE : y 0 ^ 2 + (∑ k ∈ (range L).erase h, (y k - y (k + 1)) ^ 2) + y L ^ 2 / 3 =
      lam * ((2 * ((h + 1 : ℕ) : ℝ) + 1) / 4) := by
    rw [← quarterWave_mass (n := h + 1) (by omega), ← quarterWave_energy (h + 1),
      Finset.sum_range_succ', herase, hyL]
    have hy0 : y 0 = Real.sin θ := by simp [y, gapBottomWave, θ]
    have hterm : ∀ k ∈ range h, (y k - y (k + 1)) ^ 2 =
        (Real.sin ((((k + 1 : ℕ) : ℝ) + 1) * θ) - Real.sin (((k + 1 : ℕ) : ℝ) * θ)) ^ 2 := by
      intro k hk
      have hk' := mem_range.mp hk
      simp only [y, gapBottomWave, if_pos (show k ≤ h by omega), if_pos (show k + 1 ≤ h by omega)]
      push_cast; ring
    rw [sum_congr rfl hterm, hy0]
    simp
    ring
  have hlampos : 0 < lam := mixedChainConstant_pos (h + 1)
  have hpos : 0 < fermiGapPronicEnergy N (fermiDyadicProfilePacket L y) (h + 1) := by
    apply gap_pos_of_ray_one
    have := rayGap_ge_terms N (fermiDyadicProfilePacket L y) one_pos h (h + 1) (by omega)
    have hhead : fermiNormalizedDyadicSieve N (fermiDyadicProfilePacket L y) 1 0 = y 0 := by
      unfold fermiNormalizedDyadicSieve
      rw [show (2 : ℕ) ^ 0 * 1 = 2 ^ 0 * 1 from rfl,
        sieveSeq_fermiDyadicProfilePacket_ray hLN y 0 odd_one]
      simp
    have hy0 : 0 < y 0 := by
      simp only [y, gapBottomWave, if_pos (Nat.zero_le h), Nat.cast_zero, zero_add, one_mul]
      apply Real.sin_pos_of_pos_of_lt_pi (by unfold quarterWaveAngle; positivity)
      unfold quarterWaveAngle
      rw [div_lt_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ h + 1 by omega)
      nlinarith [Real.pi_pos]
    have hw : 0 < fermiDyadicPronicWeight 0 1 := by
      unfold fermiDyadicPronicWeight pronicSeq; norm_num
    have hj : 0 ≤ fermiNormalizedDyadicJump N (fermiDyadicProfilePacket L y) 1 (h + 1) ^ 2 *
        fermiDyadicPronicWeight (h + 1 + 1) 1 :=
      mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _)
    rw [hhead] at this
    have : 0 < y 0 ^ 2 * fermiDyadicPronicWeight 0 1 := by positivity
    linarith
  have hge := fermiGapInverseConstant_ge_profilePacket hLN hhL y hy hpos
    (mul_pos hlampos (by positivity)) hE.le
  rw [hS] at hge
  rcases ratio_lower (n := h + 1) (by omega) with hr | hr
  · exact hr.trans hge
  · exact (div_nonpos_of_nonpos_of_nonneg hr (by positivity)).trans
      (fermiGapInverseConstant_nonneg N (h + 1))

/-- **Top lower bound.** For `h < L`, `2^L ≤ N`:
`K_{h+1}(N) ≥ ((2(L-h)+1)² - 8(2(L-h)+1))/π²`. -/
theorem fermiGapInverseConstant_ge_top {L N h : ℕ} (hLN : 2 ^ L ≤ N) (hhL : h < L) :
    ((2 * ((L - h : ℕ) : ℝ) + 1) ^ 2 - 8 * (2 * ((L - h : ℕ) : ℝ) + 1)) / Real.pi ^ 2 ≤
      fermiGapInverseConstant N (h + 1) := by
  set n := L - h with hn
  have hn1 : 1 ≤ n := by omega
  set y := gapTopWave L h
  set θ := quarterWaveAngle n
  have hyk (k : ℕ) (hk1 : h + 1 ≤ k) (hk2 : k ≤ L) :
      y k = Real.sin (((L + 1 - k : ℕ) : ℝ) * θ) := by
    simp only [y, gapTopWave]
    rw [if_pos (show h + 1 ≤ k ∧ k ≤ L from ⟨hk1, hk2⟩)]
  have hy0 (k : ℕ) (hk : k ≤ h) : y k = 0 := by
    simp only [y, gapTopWave]
    rw [if_neg (by omega)]
  have hy : ∀ k ≤ L, y k ^ 2 ≤ 1 := fun k _ => by
    simp only [y, gapTopWave]; split_ifs
    · exact Real.sin_sq_le_one _
    · norm_num
  -- the profile restricted to its support, read downward
  have hsupp (k : ℕ) (hk : k < n) :
      y (h + 1 + k) = Real.sin ((((n - 1 - k : ℕ) : ℝ) + 1) * θ) := by
    rw [hyk (h + 1 + k) (by omega) (by omega), show L + 1 - (h + 1 + k) = (n - 1 - k) + 1 by omega]
    push_cast; ring_nf
  have hS : (∑ k ∈ range (L + 1), y k ^ 2) = (2 * (n : ℝ) + 1) / 4 := by
    rw [← quarterWave_mass hn1]
    have hsplit := sum_range_add (fun k => y k ^ 2) (h + 1) n
    rw [show h + 1 + n = L + 1 by omega] at hsplit
    rw [hsplit]
    have hz : (∑ k ∈ range (h + 1), y k ^ 2) = 0 :=
      sum_eq_zero fun k hk => by rw [hy0 k (by have := mem_range.mp hk; omega)]; ring
    rw [hz, zero_add, sum_congr rfl fun k hk => by rw [hsupp k (mem_range.mp hk)]]
    exact sum_range_reflect (fun j => Real.sin (((j : ℝ) + 1) * θ) ^ 2) n
  set lam := 2 - 2 * Real.cos θ
  have hQW := quarterWave_energy n
  rw [quarterWave_mass hn1] at hQW
  -- the observed jumps are the quarter-wave jumps except the bottom one
  have hEdef : y 0 ^ 2 + (∑ k ∈ (range L).erase h, (y k - y (k + 1)) ^ 2) + y L ^ 2 / 3 ≤
      lam * ((2 * (n : ℝ) + 1) / 4) := by
    rw [← hQW]
    have hy00 : y 0 = 0 := hy0 0 (Nat.zero_le _)
    have hyL : y L = Real.sin ((0 + 1) * θ) := by
      rw [hyk L (by omega) le_rfl, show L + 1 - L = 1 by omega]; simp
    have herase : (∑ k ∈ (range L).erase h, (y k - y (k + 1)) ^ 2) =
        ∑ k ∈ range (n - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2 := by
      have hsub : (range (n - 1)).image (fun k => h + 1 + k) ⊆ (range L).erase h := by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
        have := mem_range.mp hk
        exact mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩
      rw [← sum_subset hsub, sum_image fun a _ b _ hab => by omega]
      intro x hx hxn
      have hx1 := mem_range.mp (mem_of_mem_erase hx)
      have hx2 : x ≠ h := ne_of_mem_erase hx
      have hxh : x < h := by
        by_contra hc
        exact hxn (mem_image.mpr ⟨x - (h + 1), mem_range.mpr (by omega), by omega⟩)
      rw [hy0 x (by omega), hy0 (x + 1) (by omega)]; ring
    rw [hy00, herase, hyL]
    -- rewrite the quarter-wave energy into its bottom jump and the remaining jumps
    have hQsplit : (∑ j ∈ range n, (Real.sin (((j : ℝ) + 1) * θ) - Real.sin ((j : ℝ) * θ)) ^ 2) =
        (∑ j ∈ range (n - 1), (Real.sin ((((j + 1 : ℕ) : ℝ) + 1) * θ) -
          Real.sin (((j + 1 : ℕ) : ℝ) * θ)) ^ 2) + Real.sin ((0 + 1) * θ) ^ 2 := by
      rw [show n = n - 1 + 1 by omega, Finset.sum_range_succ', show n - 1 + 1 - 1 = n - 1 by omega]
      simp
    have hjumps : (∑ k ∈ range (n - 1), (y (h + 1 + k) - y (h + 1 + k + 1)) ^ 2) =
        ∑ j ∈ range (n - 1), (Real.sin ((((j + 1 : ℕ) : ℝ) + 1) * θ) -
          Real.sin (((j + 1 : ℕ) : ℝ) * θ)) ^ 2 := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun k hk => ?_
      have hk' := mem_range.mp hk
      rw [show h + 1 + (n - 1 - 1 - k) + 1 = h + 1 + (n - 1 - k) by omega,
        hsupp (n - 1 - 1 - k) (by omega), hsupp (n - 1 - k) (by omega),
        show n - 1 - (n - 1 - 1 - k) = k + 1 by omega, show n - 1 - (n - 1 - k) = k by omega]
      push_cast; ring
    rw [hQsplit, hjumps]
    simp only [zero_add, one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    linarith [sq_nonneg (Real.sin θ)]
  have hlampos : 0 < lam := mixedChainConstant_pos n
  have hpos : 0 < fermiGapPronicEnergy N (fermiDyadicProfilePacket L y) (h + 1) := by
    apply gap_pos_of_ray_one
    have hterm := rayGap_ge_terms N (fermiDyadicProfilePacket L y) one_pos h L (by omega)
    have hjL : fermiNormalizedDyadicJump N (fermiDyadicProfilePacket L y) 1 L = y L / 2 := by
      rw [fermiNormalizedDyadicJump_eq_sub _ _ one_pos]
      unfold fermiNormalizedDyadicSieve
      rw [sieveSeq_fermiDyadicProfilePacket_ray hLN y L odd_one,
        sieveSeq_fermiDyadicProfilePacket_ray hLN y (L + 1) odd_one, min_self,
        min_eq_left (by omega : L ≤ L + 1), pow_succ]
      field_simp; ring
    have hyLpos : 0 < y L := by
      rw [hyk L (by omega) le_rfl, show L + 1 - L = 1 by omega, Nat.cast_one, one_mul]
      apply Real.sin_pos_of_pos_of_lt_pi (by simp only [θ]; unfold quarterWaveAngle; positivity)
      simp only [θ]; unfold quarterWaveAngle
      rw [div_lt_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      nlinarith [Real.pi_pos]
    have hw : 0 < fermiDyadicPronicWeight (L + 1) 1 := by
      unfold fermiDyadicPronicWeight pronicSeq; positivity
    have hb0 : 0 ≤ fermiNormalizedDyadicSieve N (fermiDyadicProfilePacket L y) 1 0 ^ 2 *
        fermiDyadicPronicWeight 0 1 := mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _)
    rw [hjL] at hterm
    have : 0 < (y L / 2) ^ 2 * fermiDyadicPronicWeight (L + 1) 1 := by positivity
    linarith
  have hge := fermiGapInverseConstant_ge_profilePacket hLN hhL y hy hpos
    (mul_pos hlampos (by positivity)) hEdef
  rw [hS] at hge
  rcases ratio_lower hn1 with hr | hr
  · exact hr.trans hge
  · exact (div_nonpos_of_nonpos_of_nonneg hr (by positivity)).trans
      (fermiGapInverseConstant_nonneg N (h + 1))

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
