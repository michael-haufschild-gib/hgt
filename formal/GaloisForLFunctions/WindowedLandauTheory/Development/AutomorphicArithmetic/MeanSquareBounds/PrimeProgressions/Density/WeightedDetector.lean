import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.DetectorPowerSum
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroRepulsion.LocalZeroMultisets

/-! Retain large reciprocals using the square mass of the whole local divisor. -/

open Complex Finset

namespace QH.PrimeProgressions

theorem weighted_detector_power_sum (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (w : ℂ → ℂ) (K : ℕ) (b : ℝ) (hb : 0 < b) (hb' : b ≤ 1 / 2)
    (hmass : (∑ ρ ∈ Z, (m ρ : ℝ) * ‖w (s - ρ)‖ ^ 2) ≤ (K : ℝ) * b ^ 2)
    (hnear : ∃ ρ ∈ Z, 1 ≤ m ρ ∧ 1 / 2 ≤ ‖w (s - ρ)‖) :
    ∃ j : ℕ, K + 1 ≤ j ∧ j ≤ 2 * K ∧
      (1 / (6400 * Real.exp 1)) ^ j ≤
        ‖∑ ρ ∈ Z, (m ρ : ℂ) * w (s - ρ) ^ j‖ + (K : ℝ) * b ^ j := by
  classical
  let W := Z.filter (fun ρ => b ≤ ‖w (s - ρ)‖)
  let V := Z.filter (fun ρ => ¬ b ≤ ‖w (s - ρ)‖)
  let mass (ρ : ℂ) : ℝ := (m ρ : ℝ) * ‖w (s - ρ)‖ ^ 2
  have hmass_restrict {U : Finset ℂ} (hU : U ⊆ Z) : (∑ ρ ∈ U, mass ρ) ≤ (K : ℝ) * b ^ 2 :=
    (sum_le_sum_of_subset_of_nonneg hU (fun _ _ _ => by dsimp only [mass]; positivity)).trans hmass
  have hcount : (∑ ρ ∈ W, m ρ) ≤ K := by
    suffices ((∑ ρ ∈ W, m ρ : ℕ) : ℝ) ≤ (K : ℝ) by exact_mod_cast this
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hb)).mp
    rw [Nat.cast_sum, sum_mul]
    refine (sum_le_sum (g := mass) ?_).trans (hmass_restrict (filter_subset _ _))
    intro ρ hρ
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hb.le (mem_filter.mp hρ).2 2) (Nat.cast_nonneg _)
  obtain ⟨n, v, hv⟩ := dhFlat (dhFam W m s)
  have hn : n = ∑ ρ ∈ W, m ρ := by
    simpa only [Multiset.card_map, card_val, card_univ, Fintype.card_fin, dhFam_card] using
      congrArg Multiset.card hv
  obtain ⟨ρ, hρ, hmul, hw⟩ := hnear
  have hmem : s - ρ ∈ dhFam W m s :=
    dhFam_mem W m s ρ (mem_filter.mpr ⟨hρ, hb'.trans hw⟩) hmul
  rw [← hv, Multiset.mem_map] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  have hn₁ : 1 ≤ n := Nat.succ_le_of_lt ((Nat.zero_le i.val).trans_lt i.isLt)
  obtain ⟨j, hj, hj', hdet⟩ := detector_power_sum n K hn₁ (hn.trans_le hcount)
    (fun i => w (v i)) (r := 1) one_pos ⟨i, by simpa only [hi, mul_one] using hw⟩
  have hW := dhFlat_sum v (dhFam W m s) hv (fun d => w d ^ j)
  rw [dhFam_sum] at hW
  simp only [nsmul_eq_mul] at hW
  have hj₂ : 2 ≤ j := by omega
  let f (ρ : ℂ) : ℂ := (m ρ : ℂ) * w (s - ρ) ^ j
  have hterm (ρ : ℂ) (hρ : ρ ∈ V) : ‖f ρ‖ ≤ b ^ (j - 2) * mass ρ := by
    dsimp only [f, mass]
    rw [norm_mul, Complex.norm_natCast, norm_pow]
    conv_lhs => rw [← Nat.sub_add_cancel hj₂, pow_add]
    have hsmall : ‖w (s - ρ)‖ ≤ b := le_of_lt (lt_of_not_ge (mem_filter.mp hρ).2)
    calc
      (m ρ : ℝ) * (‖w (s - ρ)‖ ^ (j - 2) * ‖w (s - ρ)‖ ^ 2) ≤
          (m ρ : ℝ) * (b ^ (j - 2) * ‖w (s - ρ)‖ ^ 2) := by gcongr
      _ = b ^ (j - 2) * ((m ρ : ℝ) * ‖w (s - ρ)‖ ^ 2) := by ring
  have hV : ‖∑ ρ ∈ V, f ρ‖ ≤ (K : ℝ) * b ^ j := by
    calc
      ‖∑ ρ ∈ V, f ρ‖ ≤ ∑ ρ ∈ V, ‖f ρ‖ := norm_sum_le _ _
      _ ≤ b ^ (j - 2) * ∑ ρ ∈ V, mass ρ := by rw [mul_sum]; exact sum_le_sum hterm
      _ ≤ b ^ (j - 2) * ((K : ℝ) * b ^ 2) :=
        mul_le_mul_of_nonneg_left (hmass_restrict (filter_subset _ _)) (by positivity)
      _ = (K : ℝ) * b ^ j := by
        rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hj₂]
  have hsplit : (∑ ρ ∈ W, f ρ) + ∑ ρ ∈ V, f ρ = ∑ ρ ∈ Z, f ρ :=
    sum_filter_add_sum_filter_not Z (fun ρ => b ≤ ‖w (s - ρ)‖) f
  have he : (∑ ρ ∈ W, f ρ) = (∑ ρ ∈ Z, f ρ) - ∑ ρ ∈ V, f ρ := eq_sub_of_add_eq hsplit
  refine ⟨j, hj, hj', ?_⟩
  calc
    _ ≤ ‖∑ ρ ∈ W, f ρ‖ := by simpa only [mul_one, hW, f] using hdet
    _ ≤ ‖∑ ρ ∈ Z, f ρ‖ + ‖∑ ρ ∈ V, f ρ‖ := by rw [he]; exact norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl hV

end QH.PrimeProgressions
