import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPolynomialWindow
import GaloisForLFunctions.RHTower.PrimeMassSharpUpper


/-!
# Half-density Mangoldt cancellation on a growing window

Discrete Abel summation transfers the full uniform Mangoldt prefix bound
to the weight `1 / sqrt n`, without differentiating the oscillatory phase.
The complete prefix includes its discarded head through the unconditional
positive prime-mass bound. Both endpoints and all prime powers are retained.
-/

namespace RHTower.Sieve
open Filter Topology
noncomputable section

private theorem norm_halfDensity_tail_le (g : ℕ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    {M N : ℕ} (hMN : M ≤ N)
    (hp : ∀ k, M ≤ k → k ≤ N →
      ‖∑ j ∈ Finset.range (k + 1), g j‖ ≤ ε * ((k : ℝ) + 1)) :
    ‖∑ k ∈ Finset.Ioc M N, (1 / Real.sqrt (k : ℝ)) • g k‖ ≤
      4 * ε * Real.sqrt ((N : ℝ) + 1) := by
  rcases hMN.eq_or_lt with rfl | hMN
  · simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    positivity
  let w : ℕ → ℝ := fun k => 1 / Real.sqrt (k : ℝ)
  have hw0 : ∀ k, 0 ≤ w k := fun k => by dsimp [w]; positivity
  have hanti : ∀ k, 0 < k → w (k + 1) ≤ w k := by
    intro k hk
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by exact_mod_cast hk))
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k))
  have hparts := Finset.sum_Ioc_by_parts w g hMN
  have hreal := Finset.sum_Ioc_by_parts w (fun _ => (1 : ℝ)) hMN
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    smul_eq_mul, Nat.cast_add, Nat.cast_one] at hreal
  have hN := mul_le_mul_of_nonneg_left (hp N hMN.le le_rfl) (hw0 N)
  have hM := mul_le_mul_of_nonneg_left (hp M le_rfl hMN.le) (hw0 (M + 1))
  have hsum :
      ‖∑ k ∈ Finset.Ioc M (N - 1),
        (w (k + 1) - w k) • ∑ j ∈ Finset.range (k + 1), g j‖ ≤
      ε * ∑ k ∈ Finset.Ioc M (N - 1),
        (w k - w (k + 1)) * ((k : ℝ) + 1) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    obtain ⟨hMk, hkN⟩ := Finset.mem_Ioc.mp hk
    have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le M) hMk
    have hdiff : w (k + 1) - w k ≤ 0 := sub_nonpos.mpr (hanti k hk0)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hdiff]
    have h := mul_le_mul_of_nonneg_left (hp k hMk.le (by omega))
      (sub_nonneg.mpr (hanti k hk0))
    convert h using 1 <;> first | rfl | ring
  have hb : ‖∑ k ∈ Finset.Ioc M N, w k • g k‖ ≤
      ε * ((∑ k ∈ Finset.Ioc M N, w k) + 2 * w (M + 1) * ((M : ℝ) + 1)) := by
    rw [hparts]
    have htri := (norm_sub_le
      (w N • ∑ j ∈ Finset.range (N + 1), g j)
      (w (M + 1) • ∑ j ∈ Finset.range (M + 1), g j))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 N),
      abs_of_nonneg (hw0 (M + 1))] at htri
    have hnorm := (norm_sub_le
      (w N • (∑ j ∈ Finset.range (N + 1), g j) -
        w (M + 1) • (∑ j ∈ Finset.range (M + 1), g j))
      (∑ k ∈ Finset.Ioc M (N - 1),
        (w (k + 1) - w k) • ∑ j ∈ Finset.range (k + 1), g j)).trans
      (add_le_add (htri.trans (add_le_add hN hM)) hsum)
    have hneg : (∑ k ∈ Finset.Ioc M (N - 1),
        (w k - w (k + 1)) * ((k : ℝ) + 1)) =
        -(∑ k ∈ Finset.Ioc M (N - 1),
          (w (k + 1) - w k) * ((k : ℝ) + 1)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hneg] at hnorm
    nlinarith only [hnorm, congrArg (fun t : ℝ => ε * t) hreal]
  have hs : (∑ k ∈ Finset.Ioc M N, w k) ≤ 2 * Real.sqrt (N : ℝ) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hw0 k)).trans
      (RHTower.sum_one_div_sqrt_le N)
    intro k hk
    obtain ⟨hMk, hkN⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, hkN⟩
  have he : w (M + 1) * ((M : ℝ) + 1) = Real.sqrt ((M : ℝ) + 1) := by
    dsimp [w]
    rw [Nat.cast_add, Nat.cast_one]
    rw [one_div_mul_eq_div, Real.div_sqrt]
  have hroot := Real.sqrt_le_sqrt (show (M : ℝ) + 1 ≤ (N : ℝ) + 1 by exact_mod_cast Nat.succ_le_succ hMN.le)
  have hrootN := Real.sqrt_le_sqrt (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
  change ‖∑ k ∈ Finset.Ioc M N, w k • g k‖ ≤ _
  refine hb.trans ?_
  rw [mul_assoc 2 (w (M + 1)), he]
  calc ε * ((∑ k ∈ Finset.Ioc M N, w k) + 2 * Real.sqrt ((M : ℝ) + 1))
      ≤ ε * (4 * Real.sqrt ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hε
    _ = _ := by ring

/-- Uniform cancellation survives the half-density weight on every tail
inside the growing cutoff window. The sequence retains all prime powers. -/
theorem eventually_norm_vonMangoldtTwist_halfDensity_tail_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (M N : ℕ) (τ : ℝ), M ≤ N →
      twoRangeXmin ((19 : ℝ) / 20) x ≤ (M : ℝ) →
      Real.log (N : ℝ) ≤ twoRangeLx 2 x →
      twoRangeT₀ 2 100 x ≤ |τ| → |τ| ≤ 2 * Real.pi * x →
      ‖∑ n ∈ Finset.Ioc M N, (1 / Real.sqrt (n : ℝ)) • vonMangoldtTwist τ n‖ ≤
        4 * ε * Real.sqrt ((N : ℝ) + 1) := by
  filter_upwards [eventually_norm_vonMangoldtTwist_prefix_le_polynomialWindow ε hε]
    with x hx
  intro M N τ hMN hM hN hlo hhi
  refine norm_halfDensity_tail_le _ hε.le hMN (fun k hMk hkN => ?_)
  have hk : twoRangeXmin ((19 : ℝ) / 20) x ≤ (k : ℝ) :=
    hM.trans (Nat.cast_le.mpr hMk)
  have hk0 : (0 : ℝ) < k := (twoRangeXmin_pos _ _).trans_le hk
  have hlog : Real.log (k : ℝ) ≤ twoRangeLx 2 x :=
    (Real.log_le_log hk0 (Nat.cast_le.mpr hkN)).trans hN
  exact (hx k τ hk hlog hlo hhi).trans
    (mul_le_mul_of_nonneg_left (by linarith) hε.le)

private theorem norm_halfDensity_prefix_le_primeMass (τ : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range (N + 1), (1 / Real.sqrt (n : ℝ)) • vonMangoldtTwist τ n‖ ≤
      primeMassHalf (N : ℝ) := by
  refine (norm_sum_le _ _).trans_eq ?_
  have hset : Finset.range (N + 1) = Finset.Icc 0 N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_Icc, Nat.zero_le, true_and]
    omega
  rw [primeMassHalf, Nat.floor_natCast, hset]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (n : ℝ)), norm_vonMangoldtTwist]
  ring

/-- The complete half-density prefix, with its small-cutoff head retained.
This is the high-frequency arithmetic input for the prime-polar multiplier. -/
theorem eventually_norm_vonMangoldtTwist_halfDensity_prefix_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (M N : ℕ) (τ : ℝ), M ≤ N →
      twoRangeXmin ((19 : ℝ) / 20) x ≤ (M : ℝ) →
      Real.log (N : ℝ) ≤ twoRangeLx 2 x →
      twoRangeT₀ 2 100 x ≤ |τ| → |τ| ≤ 2 * Real.pi * x →
      ‖∑ n ∈ Finset.range (N + 1), (1 / Real.sqrt (n : ℝ)) • vonMangoldtTwist τ n‖ ≤
        21 * Real.sqrt (M : ℝ) + 4 * ε * Real.sqrt ((N : ℝ) + 1) := by
  filter_upwards [eventually_norm_vonMangoldtTwist_halfDensity_tail_le ε hε]
    with x hx
  intro M N τ hMN hM hN hlo hhi
  have hM0 : 0 < M := by exact_mod_cast (twoRangeXmin_pos _ _).trans_le hM
  have hhead := (norm_halfDensity_prefix_le_primeMass τ M).trans
    (primeMassHalf_le_sqrt (by exact_mod_cast hM0))
  have htail := hx M N τ hMN hM hN hlo hhi
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n => (1 / Real.sqrt (n : ℝ)) • vonMangoldtTwist τ n)
    (Nat.succ_le_succ hMN)
  simp only [Nat.succ_eq_add_one] at hsplit
  rw [Finset.Ico_add_one_add_one_eq_Ioc] at hsplit
  rw [← hsplit]
  exact (norm_add_le _ _).trans (add_le_add hhead htail)

end
end RHTower.Sieve
