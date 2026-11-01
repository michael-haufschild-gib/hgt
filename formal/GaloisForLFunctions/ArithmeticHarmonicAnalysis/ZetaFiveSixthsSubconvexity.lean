import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiveSixthsSubconvexityBlocks
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.SubconvexityDyadicTruncation

/-! # The zeta exponent `2/53` on `Re s=5/6`

Euler–Maclaurin truncation, a trivial head and the three logarithmic block
regimes give an unconditional bound `O(t^(2/53) log t)`.
-/

noncomputable section
open RHTower RHTower.Sieve Complex

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- An unconditional interior subconvexity bound at `Re s=5/6`. -/
theorem norm_riemannZeta_fiveSixths_le {t : ℝ} (ht : 8 ≤ t) :
    ‖riemannZeta ((5 / 6 : ℂ) + (t : ℂ) * I)‖ ≤ 10 ^ 7 * t ^ (2 / 53 : ℝ) * Real.log t := by
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hlogt : 2 ≤ Real.log t := by
    have h8 := Real.log_le_log (by norm_num : (0 : ℝ) < 8) ht
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow] at h8
    have hl2 := Real.log_two_gt_d9
    norm_num only [Nat.cast_ofNat] at h8
    linarith only [h8, hl2]
  have hmu : 1 ≤ t ^ (2 / 53 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hx1 : 1 ≤ t ^ (12 / 53 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ⌈t ^ (12 / 53 : ℝ)⌉₊ + 3 := ⟨_, rfl⟩
  have hc3 : 3 ≤ c := by omega
  have hc0 : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hclower : t ^ (12 / 53 : ℝ) ≤ (c : ℝ) := by
    have h := Nat.le_ceil (t ^ (12 / 53 : ℝ))
    rw [hc]
    push_cast
    linarith only [h]
  have hcup : (c : ℝ) ≤ t ^ (12 / 53 : ℝ) + 4 := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ t ^ (12 / 53 : ℝ))
    rw [hc]
    push_cast
    linarith only [h]
  have hcup5 : (c : ℝ) ≤ 5 * t ^ (12 / 53 : ℝ) := by linarith only [hcup, hx1]
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = zetaDyadicTruncationExponent t := ⟨_, rfl⟩
  obtain ⟨hRlo, hRup, hRlog⟩ := zetaDyadicTruncation_bounds ht
  rw [← hR] at hRlo hRup hRlog
  have hpower : t ^ (12 / 53 : ℝ) * t ^ (2 : ℕ) = t ^ (118 / 53 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
    norm_num
  have hMup : (c : ℝ) * 2 ^ R ≤ 20 * t ^ (118 / 53 : ℝ) := by
    have h := mul_le_mul hcup5 hRup (by positivity) (by positivity)
    calc _ ≤ (5 * t ^ (12 / 53 : ℝ)) * (4 * t ^ 2) := h
      _ = 20 * (t ^ (12 / 53 : ℝ) * t ^ (2 : ℕ)) := by ring
      _ = _ := by rw [hpower]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = c * 2 ^ R - 1 := ⟨_, rfl⟩
  have hKR : (K : ℝ) = (c : ℝ) * 2 ^ R - 1 := by
    rw [hK, Nat.cast_sub (by
      have hpow : 1 ≤ 2 ^ R := Nat.one_le_two_pow
      nlinarith only [hc3, hpow])]
    push_cast
    ring
  have hKlow : t ^ 2 ≤ (K : ℝ) := by
    have hcR : (3 : ℝ) * 2 ^ R ≤ (c : ℝ) * 2 ^ R :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc3) (by positivity)
    have ht2 : (1 : ℝ) ≤ t ^ 2 := by
      simpa only [one_pow] using pow_le_pow_left₀ zero_le_one ht1 2
    rw [hKR]
    linarith only [hcR, hRlo, ht2]
  have hK1 : 1 ≤ K := by
    have h1 : (1 : ℝ) ≤ K := le_trans (by nlinarith only [ht1]) hKlow
    exact_mod_cast h1
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKup : (K : ℝ) ≤ 20 * t ^ (118 / 53 : ℝ) := by rw [hKR]; linarith only [hMup]
  have hbound : ∀ r < R,
      ‖∑ n ∈ Finset.Ico (c * 2 ^ r) (c * 2 ^ (r + 1)),
        (n : ℂ) ^ (-((5 / 6 : ℝ) : ℂ) - I * (t : ℂ))‖ ≤ 10 ^ 6 * t ^ (2 / 53 : ℝ) := by
    intro r hr
    have hN1 : 1 ≤ c * 2 ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hblk : c * 2 ^ (r + 1) = 2 * (c * 2 ^ r) := by ring
    rw [hblk]
    refine norm_fiveSixthsBlock_le ht1 hN1 (by omega) le_rfl ?_ ?_
    · have hcN : (c : ℝ) ≤ ((c * 2 ^ r : ℕ) : ℝ) := by
        push_cast
        exact le_mul_of_one_le_right hc0.le (one_le_pow₀ (by norm_num))
      have hl := Real.log_le_log (by positivity) (hclower.trans hcN)
      rw [Real.log_rpow ht0] at hl
      linarith only [hl]
    · have h2N : 2 * ((c * 2 ^ r : ℕ) : ℝ) ≤ (c : ℝ) * 2 ^ R := by
        have hp : (2 : ℝ) ^ (r + 1) ≤ 2 ^ R := pow_le_pow_right₀ (by norm_num) (by omega)
        have hm := mul_le_mul_of_nonneg_left hp hc0.le
        push_cast
        rw [pow_succ] at hm
        nlinarith only [hm]
      have hNup : ((c * 2 ^ r : ℕ) : ℝ) ≤ 10 * t ^ (118 / 53 : ℝ) := by
        linarith only [h2N, hMup]
      exact hNup.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (118 / 53 : ℝ) ≤ 7 / 3)) (by norm_num))
  have hhead : 1 + (((c - 1 : ℕ) : ℝ) ^ (1 - 5 / 6 : ℝ) - 1) / (1 - 5 / 6) +
      ((c - 1 : ℕ) : ℝ) ^ (-(5 / 6 : ℝ)) ≤ 30 * t ^ (2 / 53 : ℝ) := by
    have hc1 : (1 : ℝ) ≤ ((c - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ c - 1 by omega)
    have hcle : ((c - 1 : ℕ) : ℝ) ≤ 4 * t ^ (12 / 53 : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith only [hcup, hx1]
    have hneg : ((c - 1 : ℕ) : ℝ) ^ (-(5 / 6 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have hp : ((c - 1 : ℕ) : ℝ) ^ (1 / 6 : ℝ) ≤ 4 * t ^ (2 / 53 : ℝ) := by
      refine (Real.rpow_le_rpow (by positivity) hcle (by norm_num)).trans ?_
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul ht0.le]
      norm_num only [show (12 / 53 : ℝ) * (1 / 6) = 2 / 53 by norm_num]
      exact mul_le_mul_of_nonneg_right
        (rpow_le_self_of_le_one (by norm_num) (by norm_num)) (by positivity)
    norm_num only [show (1 - 5 / 6 : ℝ) = 1 / 6 by norm_num]
    linarith only [hp, hneg, hmu]
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (5 / 6 : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  rw [← hw]
  have hwre : w.re = 5 / 6 := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have hw1 : w ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    rw [hwim, Complex.one_im] at hi
    linarith only [hi, ht0]
  have htail1 : (K : ℝ) ^ (1 - 5 / 6 : ℝ) / ‖w - 1‖ ≤ 20 := by
    have hnorm : t ≤ ‖w - 1‖ := by
      have h := Complex.abs_im_le_norm (w - 1)
      simpa only [Complex.sub_im, hwim, Complex.one_im, sub_zero, abs_of_pos ht0] using h
    have hlogK := Real.log_le_log hK0 hKup
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow ht0] at hlogK
    have hl20 : 0 ≤ Real.log (20 : ℝ) := Real.log_nonneg (by norm_num)
    have hp : (K : ℝ) ^ (1 - 5 / 6 : ℝ) ≤ 20 * t := by
      refine le_of_log_le_log (by positivity) (by positivity) ?_
      rw [Real.log_rpow hK0, Real.log_mul (by norm_num) ht0.ne']
      linarith only [hlogK, hlogt, hl20]
    rw [div_le_iff₀ (ht0.trans_le hnorm)]
    exact hp.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))
  have htail2 : ‖w‖ * ((K : ℝ) ^ (-(5 / 6 : ℝ)) / (5 / 6)) ≤ 3 := by
    have hwn : ‖w‖ ≤ 2 * t := by
      rw [hw]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      norm_num
      linarith only [ht1]
    have hlogK := Real.log_le_log (by positivity : 0 < t ^ 2) hKlow
    rw [Real.log_pow] at hlogK
    norm_num only [Nat.cast_ofNat] at hlogK
    have hKn : (K : ℝ) ^ (-(5 / 6 : ℝ)) ≤ t⁻¹ := by
      refine le_of_log_le_log (by positivity) (by positivity) ?_
      rw [Real.log_rpow hK0, Real.log_inv]
      linarith only [hlogK, hlogt]
    calc _ ≤ (2 * t) * (t⁻¹ / (5 / 6)) := by gcongr
      _ = 12 / 5 := by field_simp; ring
      _ ≤ 3 := by norm_num
  have htrunc := norm_riemannZeta_le_partialSum (w := w) (by rw [hwre]; norm_num) hw1 hK1
  rw [hwre] at htrunc
  have hsum : (∑ k ∈ Finset.Icc 1 K, ((k : ℝ) : ℂ) ^ (-w)) =
      ∑ n ∈ Finset.Ico 1 (c * 2 ^ R), (n : ℂ) ^ (-((5 / 6 : ℝ) : ℂ) - I * (t : ℂ)) := by
    have hIco : Finset.Ico 1 (c * 2 ^ R) = Finset.Icc 1 K := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc, hK]
      omega
    rw [hIco]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hw]
    push_cast
    ring_nf
  rw [hsum] at htrunc
  have hblocks := norm_dirichlet_sigma_partial_of_blockBound (σ := 5 / 6) (t := t)
    (by norm_num) (by norm_num) hc3 (fun _ => 10 ^ 6 * t ^ (2 / 53 : ℝ)) (R := R) hbound
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hblocks
  have hR' := mul_le_mul_of_nonneg_right hRlog (by positivity : 0 ≤ 10 ^ 6 * t ^ (2 / 53 : ℝ))
  have hm := mul_le_mul_of_nonneg_left hlogt (by positivity : 0 ≤ t ^ (2 / 53 : ℝ))
  nlinarith only [htrunc, hblocks, hhead, htail1, htail2, hR', hm, hmu]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_riemannZeta_fiveSixths_le
