import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheChainIsBoundedAtHalfDamping
import GaloisForLFunctions.RHTower.RieszMoebiusMeansOnTheOneLine

/-!
# The chain is compact at half damping

The centred damping chain at half damping is compact on `ℓ²`, although it is not
Hilbert–Schmidt: on vectors supported beyond `K` its energy is `≪ K^{−1/10}`,
`Σ_{n<T} (C_{½} b)(n)² ≤ M K^{−1/10} Σ_k b_k²` for every finitely supported `b` vanishing below
`K` and every horizon `T` (`exists_centeredOperator_tail_l2_le_half`), uniformly for `½ < η < 1`
(`exists_centeredOperator_tail_l2_le_uniform`). So `C_{½}` is the operator-norm limit of its
finite sections `C_{½} Π_K` (`centeredOperator_half_tail_small`).

**Proof.** For `b` vanishing below `K`, `(Σ_k |b_k|/(k+1))² ≤ Σ_k b_k²/K`
(`sq_sum_abs_div_succ_le_of_vanish`). This makes the floor correction of the discretization small
(`sum_sq_centeredOperator_le_integral_add`) and the dilation symbol small pointwise,
`|B(t)|² ≤ |z|² Σ b_k²/K` (`norm_sq_dilationSymbol_le_of_vanish`). Below the height `K^{½}` this
pointwise bound against the critical weight `|M P|² ≪ t^{3/4} log⁴ t / t²` costs `≪ K^{−7/64}`
(`integral_weighted_symbol_below_le`); above it the dyadic shells of the boundedness proof cost
`≪ K^{−7/64}` as well (`shell_base_constant_le`).
-/

open MeasureTheory Set Filter Topology Complex
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Vectors supported beyond `K` -/

/-- `Σ_{K ≤ k < N} 1/(k+1)² ≤ 1/K`. -/
theorem sum_inv_succ_sq_of_le {K : ℕ} (hK : 1 ≤ K) (N : ℕ) :
    ∑ k ∈ Finset.range N, (if K ≤ k then (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 else 0) ≤ 1 / (K : ℝ) := by
  have key : ∀ N : ℕ, ∑ k ∈ Finset.range N, (if K ≤ k then (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 else 0) ≤
      1 / (K : ℝ) - 1 / ((max N K : ℕ) : ℝ) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      split_ifs with h
      · have hn : (1 : ℝ) ≤ n := by exact_mod_cast hK.trans h
        have hn0 : (0 : ℝ) < n := by linarith
        rw [max_eq_left h] at ih
        rw [max_eq_left (by omega : K ≤ n + 1)]
        have hstep : (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
          push_cast
          rw [div_pow, one_pow, div_sub_div _ _ (ne_of_gt hn0) (by positivity : (n : ℝ) + 1 ≠ 0),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
      · rw [max_eq_right (by omega : n ≤ K)] at ih
        rw [max_eq_right (by omega : n + 1 ≤ K)]
        linarith
  have hM : (0 : ℝ) ≤ 1 / ((max N K : ℕ) : ℝ) := by positivity
  linarith [key N]

/-- **Vectors supported beyond `K`**: `(Σ_k |b_k|/(k+1))² ≤ Σ_k b_k² / K`. -/
theorem sq_sum_abs_div_succ_le_of_vanish {K : ℕ} (hK : 1 ≤ K) (N : ℕ) {b : ℕ → ℝ}
    (hlow : ∀ k, k < K → b k = 0) :
    (∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ))) ^ 2 ≤
      (∑ k ∈ Finset.range N, b k ^ 2) / K := by
  have hrw : ∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range N, |b k| * (if K ≤ k then 1 / ((k + 1 : ℕ) : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · rfl
    · simp [hlow k (by omega)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N) (fun k => |b k|)
    (fun k => if K ≤ k then 1 / ((k + 1 : ℕ) : ℝ) else 0)
  have hsq : ∑ k ∈ Finset.range N, (if K ≤ k then 1 / ((k + 1 : ℕ) : ℝ) else 0) ^ 2 =
      ∑ k ∈ Finset.range N, (if K ≤ k then (1 / ((k + 1 : ℕ) : ℝ)) ^ 2 else 0) :=
    Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
  have hnb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [hrw]
  calc _ ≤ (∑ k ∈ Finset.range N, |b k| ^ 2) *
        ∑ k ∈ Finset.range N, (if K ≤ k then 1 / ((k + 1 : ℕ) : ℝ) else 0) ^ 2 := hcs
    _ ≤ (∑ k ∈ Finset.range N, b k ^ 2) * (1 / K) := by
        rw [hsq, Finset.sum_congr rfl fun k _ => sq_abs (b k)]
        exact mul_le_mul_of_nonneg_left (sum_inv_succ_sq_of_le hK N) hnb0
    _ = _ := by ring

/-- **The symbol of a vector supported beyond `K`**: `‖B(t)‖² ≤ ‖z‖² Σ_k b_k² / K`. -/
theorem norm_sq_dilationSymbol_le_of_vanish {η : ℝ} (h0 : 1 / 2 < η) {K : ℕ} (hK : 1 ≤ K)
    (N : ℕ) {b : ℕ → ℝ} (hlow : ∀ k, k < K → b k = 0) (t : ℝ) :
    ‖dilationSymbol η N b t‖ ^ 2 ≤
      ‖(((-1 / 2 : ℝ) : ℂ) + t * I) - η‖ ^ 2 * ((∑ k ∈ Finset.range N, b k ^ 2) / K) := by
  set Z := ‖(((-1 / 2 : ℝ) : ℂ) + t * I) - η‖
  have h1 : ‖dilationSymbol η N b t‖ ≤
      Z * ∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ)) := by
    unfold dilationSymbol
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      rw [mul_one_div]; exact norm_dilationTerm_le h0 b t k
  calc ‖dilationSymbol η N b t‖ ^ 2
      ≤ (Z * ∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = Z ^ 2 * (∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ))) ^ 2 := by ring
    _ ≤ Z ^ 2 * ((∑ k ∈ Finset.range N, b k ^ 2) / K) :=
        mul_le_mul_of_nonneg_left (sq_sum_abs_div_succ_le_of_vanish hK N hlow) (sq_nonneg _)

/-! ### The weighted symbol beyond `K` -/

/-- Below the height `T₁ ≥ T₀` the weighted symbol of a vector supported beyond `K` costs
`T₁ ((9/4 + T₀²) C₁ + 2 · 128⁴ C₂ T₁^{25/32}) Σ_k b_k²/K`. -/
theorem integral_weighted_symbol_below_le {η T₀ C₁ C₂ T₁ : ℝ} (h0 : 1 / 2 < η) (h1 : η < 1)
    (hT₀ : 8 ≤ T₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hT₁ : T₀ ≤ T₁)
    (hw1 : ∀ t, |t| ≤ T₀ → criticalSourceWeight η t ≤ C₁)
    (hw2 : ∀ t, T₀ ≤ |t| →
      criticalSourceWeight η t ≤ C₂ * (|t| ^ (3 / 4 : ℝ) * Real.log |t| ^ 4 / t ^ 2))
    {K : ℕ} (hK : 1 ≤ K) (N : ℕ) {b : ℕ → ℝ} (hlow : ∀ k, k < K → b k = 0)
    (hFi : IntervalIntegrable (fun t => ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t)
      volume 0 T₁) :
    ∫ t in (0 : ℝ)..T₁, ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t ≤
      T₁ * ((9 / 4 + T₀ ^ 2) * C₁ + 2 * 128 ^ 4 * C₂ * T₁ ^ (25 / 32 : ℝ)) *
        ((∑ k ∈ Finset.range N, b k ^ 2) / K) := by
  have hnbK : 0 ≤ (∑ k ∈ Finset.range N, b k ^ 2) / (K : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) (Nat.cast_nonneg _)
  set nbK := (∑ k ∈ Finset.range N, b k ^ 2) / (K : ℝ)
  have hT₁0 : 0 ≤ T₁ := by linarith
  have hE0 : 0 ≤ 2 * 128 ^ 4 * C₂ * T₁ ^ (25 / 32 : ℝ) := by positivity
  have hD0 : 0 ≤ (9 / 4 + T₀ ^ 2) * C₁ := by positivity
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T₁, ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t ≤
      ((9 / 4 + T₀ ^ 2) * C₁ + 2 * 128 ^ 4 * C₂ * T₁ ^ (25 / 32 : ℝ)) * nbK := by
    intro t ht
    have hW0 : 0 ≤ criticalSourceWeight η t := by unfold criticalSourceWeight; positivity
    have hB' : ‖dilationSymbol η N b t‖ ^ 2 ≤ (9 / 4 + t ^ 2) * nbK :=
      (norm_sq_dilationSymbol_le_of_vanish h0 hK N hlow t).trans
        (mul_le_mul_of_nonneg_right (norm_sq_critical_sub_le h0 h1 t) hnbK)
    rcases le_total t T₀ with htT | htT
    · -- low heights: the weight is bounded
      have hW := hw1 t (by rw [abs_of_nonneg ht.1]; exact htT)
      have ht2 : 9 / 4 + t ^ 2 ≤ 9 / 4 + T₀ ^ 2 := by nlinarith [ht.1]
      calc ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t
          ≤ ((9 / 4 + t ^ 2) * nbK) * C₁ :=
            mul_le_mul hB' hW hW0 (mul_nonneg (by positivity) hnbK)
        _ ≤ ((9 / 4 + T₀ ^ 2) * nbK) * C₁ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht2 hnbK) hC₁
        _ = (9 / 4 + T₀ ^ 2) * C₁ * nbK := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hnbK
    · -- middle heights: `t² |M P|² ≪ t^{3/4} log⁴ t ≤ 128⁴ t^{25/32}`
      have ht0 : 0 < t := by linarith
      have hta : |t| = t := abs_of_pos ht0
      have hW := hw2 t (by rw [hta]; exact htT)
      rw [hta, ← mul_div_assoc] at hW
      have hWt : criticalSourceWeight η t * t ^ 2 ≤ C₂ * (t ^ (3 / 4 : ℝ) * Real.log t ^ 4) :=
        (le_div_iff₀ (by positivity)).mp hW
      have hlog : Real.log t ^ 4 ≤ 128 ^ 4 * t ^ (1 / 32 : ℝ) :=
        (RHTower.log_pow_le_rpow_one_div_32 (by linarith : (1 : ℝ) ≤ t) (k := 4)
          (by norm_num)).trans (le_of_eq (by norm_num))
      have hpow : t ^ (3 / 4 : ℝ) * Real.log t ^ 4 ≤ 128 ^ 4 * T₁ ^ (25 / 32 : ℝ) := by
        have e : t ^ (3 / 4 : ℝ) * t ^ (1 / 32 : ℝ) = t ^ (25 / 32 : ℝ) := by
          rw [← Real.rpow_add ht0]; norm_num
        calc t ^ (3 / 4 : ℝ) * Real.log t ^ 4
            ≤ t ^ (3 / 4 : ℝ) * (128 ^ 4 * t ^ (1 / 32 : ℝ)) :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = 128 ^ 4 * t ^ (25 / 32 : ℝ) := by rw [← e]; ring
          _ ≤ 128 ^ 4 * T₁ ^ (25 / 32 : ℝ) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0.le ht.2 (by norm_num))
                (by norm_num)
      have ht2 : 9 / 4 + t ^ 2 ≤ 2 * t ^ 2 := by nlinarith
      have h2n : 0 ≤ 2 * nbK := mul_nonneg (by norm_num) hnbK
      calc ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t
          ≤ ((9 / 4 + t ^ 2) * nbK) * criticalSourceWeight η t :=
            mul_le_mul_of_nonneg_right hB' hW0
        _ ≤ ((2 * t ^ 2) * nbK) * criticalSourceWeight η t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht2 hnbK) hW0
        _ = 2 * nbK * (criticalSourceWeight η t * t ^ 2) := by ring
        _ ≤ 2 * nbK * (C₂ * (t ^ (3 / 4 : ℝ) * Real.log t ^ 4)) :=
            mul_le_mul_of_nonneg_left hWt h2n
        _ ≤ 2 * nbK * (C₂ * (128 ^ 4 * T₁ ^ (25 / 32 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC₂) h2n
        _ = 2 * 128 ^ 4 * C₂ * T₁ ^ (25 / 32 : ℝ) * nbK := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hnbK
  refine (intervalIntegral.integral_mono_on hT₁0 hFi intervalIntegrable_const hpt).trans
    (le_of_eq ?_)
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The shell constant at a base height `T₁ ≥ 8`:
`T₁^{−1/4} (1 + log 2 + log T₁)⁵ ≤ 2 · 320⁵ · T₁^{−7/32}`. -/
theorem shell_base_constant_le {T₁ : ℝ} (hT₁ : 8 ≤ T₁) :
    T₁ ^ (-(1 / 4 : ℝ)) * (1 + Real.log 2 + Real.log T₁) ^ 5 ≤
      2 * 320 ^ 5 * T₁ ^ (-(7 / 32 : ℝ)) := by
  have hT0 : 0 < T₁ := by linarith
  have hL : Real.log 2 + Real.log T₁ = Real.log (2 * T₁) :=
    (Real.log_mul (by norm_num) hT0.ne').symm
  have hL1 : 1 ≤ Real.log (2 * T₁) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have h5 : (1 + Real.log 2 + Real.log T₁) ^ 5 ≤ 32 * Real.log (2 * T₁) ^ 5 := by
    rw [add_assoc, hL]
    calc (1 + Real.log (2 * T₁)) ^ 5 ≤ (2 * Real.log (2 * T₁)) ^ 5 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 5
      _ = 32 * Real.log (2 * T₁) ^ 5 := by ring
  have hlog : Real.log (2 * T₁) ^ 5 ≤ 160 ^ 5 * (2 * T₁) ^ (1 / 32 : ℝ) :=
    (RHTower.log_pow_le_rpow_one_div_32 (by linarith : (1 : ℝ) ≤ 2 * T₁) (k := 5)
      (by norm_num)).trans (le_of_eq (by norm_num))
  have h2 : (2 * T₁) ^ (1 / 32 : ℝ) ≤ 2 * T₁ ^ (1 / 32 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hT0.le]
    have h2' : (2 : ℝ) ^ (1 / 32 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 32 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right h2' (Real.rpow_nonneg hT0.le _)
  have e : T₁ ^ (-(1 / 4 : ℝ)) * T₁ ^ (1 / 32 : ℝ) = T₁ ^ (-(7 / 32 : ℝ)) := by
    rw [← Real.rpow_add hT0]; norm_num
  calc T₁ ^ (-(1 / 4 : ℝ)) * (1 + Real.log 2 + Real.log T₁) ^ 5
      ≤ T₁ ^ (-(1 / 4 : ℝ)) * (32 * (160 ^ 5 * (2 * T₁ ^ (1 / 32 : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left (h5.trans ?_) (by positivity)
        refine mul_le_mul_of_nonneg_left (hlog.trans ?_) (by norm_num)
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 2 * 320 ^ 5 * (T₁ ^ (-(1 / 4 : ℝ)) * T₁ ^ (1 / 32 : ℝ)) := by ring
    _ = 2 * 320 ^ 5 * T₁ ^ (-(7 / 32 : ℝ)) := by rw [e]

/-- **The weighted symbol of a vector supported beyond `K` is small**, uniformly in `½ < η < 1`:
`∫ |B(t)|² |M P(−½ + it)|² dt ≤ M K^{−7/64} Σ_k b_k²`. -/
theorem exists_integral_weighted_symbol_tail_le :
    ∃ M K₁ : ℝ, 0 ≤ M ∧ ∀ η : ℝ, 1 / 2 < η → η < 1 → ∀ (N K : ℕ) (b : ℕ → ℝ), K₁ ≤ K →
      (∀ k, N ≤ k → b k = 0) → (∀ k, k < K → b k = 0) →
      ∫ t : ℝ, ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t ≤
        M * (K : ℝ) ^ (-(7 / 64 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 := by
  obtain ⟨T₀, C₁, C₂, hT₀, hC₁, hC₂, hw⟩ := exists_norm_mellin_sourceProfile_sq_le
  have hr0 : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
  have hr1 : (2 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsum5 := summable_succ_pow_five_mul_geometric hr0 hr1
  have hS0 : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ j :=
    tsum_nonneg fun j => by positivity
  refine ⟨2 * ((9 / 4 + T₀ ^ 2) * C₁ + 2 * 128 ^ 4 * C₂ +
      400 * C₂ * (2 * 320 ^ 5) * ∑' j : ℕ, ((j : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ (-(1 / 4 : ℝ))) ^ j),
    T₀ ^ 2, by positivity, fun η h0 h1 N K b hK hb hlow => ?_⟩
  have hnb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hK64 : (64 : ℝ) ≤ K := le_trans (by nlinarith) hK
  have hK1 : (1 : ℝ) ≤ K := by linarith
  have hK1' : 1 ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ, T₁ = (K : ℝ) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hT₁T₀ : T₀ ≤ T₁ := by
    have h := Real.rpow_le_rpow (by positivity) hK (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rwa [← Real.sqrt_eq_rpow, Real.sqrt_sq (by linarith), ← hT₁] at h
  have hT₁8 : 8 ≤ T₁ := hT₀.trans hT₁T₀
  have hT₁0 : 0 < T₁ := by linarith
  by_cases hFi : Integrable fun t => ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t
  swap
  · rw [integral_undef hFi]
    positivity
  have hwη := hw η h0 h1
  have hlowI := integral_weighted_symbol_below_le h0 h1 hT₀ hC₁ hC₂ hT₁T₀
    (fun t ht => (hwη t).1 ht) (fun t ht => (hwη t).2 ht) hK1' N hlow hFi.intervalIntegrable
  -- the part below `K^{½}` in powers of `K`
  have e1 : T₁ / (K : ℝ) = (K : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hT₁, div_eq_iff hK0.ne', ← Real.rpow_add_one hK0.ne']; norm_num
  have e2 : T₁ * T₁ ^ (25 / 32 : ℝ) / K = (K : ℝ) ^ (-(7 / 64 : ℝ)) := by
    rw [hT₁, ← Real.rpow_mul hK0.le, ← Real.rpow_add hK0, div_eq_iff hK0.ne',
      ← Real.rpow_add_one hK0.ne']
    norm_num
  have hKexp : (K : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (K : ℝ) ^ (-(7 / 64 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
  have hD0 : 0 ≤ (9 / 4 + T₀ ^ 2) * C₁ := by positivity
  have hlowK : T₁ * ((9 / 4 + T₀ ^ 2) * C₁ + 2 * 128 ^ 4 * C₂ * T₁ ^ (25 / 32 : ℝ)) *
      ((∑ k ∈ Finset.range N, b k ^ 2) / K) ≤
      ((9 / 4 + T₀ ^ 2) * C₁ + 2 * 128 ^ 4 * C₂) * (K : ℝ) ^ (-(7 / 64 : ℝ)) *
        ∑ k ∈ Finset.range N, b k ^ 2 := by
    calc T₁ * ((9 / 4 + T₀ ^ 2) * C₁ + 2 * 128 ^ 4 * C₂ * T₁ ^ (25 / 32 : ℝ)) *
          ((∑ k ∈ Finset.range N, b k ^ 2) / K)
        = (9 / 4 + T₀ ^ 2) * C₁ * (T₁ / K) * ∑ k ∈ Finset.range N, b k ^ 2 +
            2 * 128 ^ 4 * C₂ * (T₁ * T₁ ^ (25 / 32 : ℝ) / K) * ∑ k ∈ Finset.range N, b k ^ 2 := by
          ring
      _ = (9 / 4 + T₀ ^ 2) * C₁ * (K : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 +
            2 * 128 ^ 4 * C₂ * (K : ℝ) ^ (-(7 / 64 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 := by
          rw [e1, e2]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKexp hD0) hnb0
          linarith
  -- the shells above `K^{½}`
  obtain ⟨A, hA⟩ : ∃ A : ℝ,
      A = 400 * C₂ * T₁ ^ (-(1 / 4 : ℝ)) * (1 + Real.log 2 + Real.log T₁) ^ 5 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    have : 0 ≤ Real.log T₁ := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hAK : A ≤ 400 * C₂ * (2 * 320 ^ 5) * (K : ℝ) ^ (-(7 / 64 : ℝ)) := by
    have e3 : T₁ ^ (-(7 / 32 : ℝ)) = (K : ℝ) ^ (-(7 / 64 : ℝ)) := by
      rw [hT₁, ← Real.rpow_mul hK0.le]; norm_num
    rw [hA]
    calc 400 * C₂ * T₁ ^ (-(1 / 4 : ℝ)) * (1 + Real.log 2 + Real.log T₁) ^ 5
        = 400 * C₂ * (T₁ ^ (-(1 / 4 : ℝ)) * (1 + Real.log 2 + Real.log T₁) ^ 5) := by ring
      _ ≤ 400 * C₂ * (2 * 320 ^ 5 * T₁ ^ (-(7 / 32 : ℝ))) :=
          mul_le_mul_of_nonneg_left (shell_base_constant_le hT₁8) (by positivity)
      _ = _ := by rw [e3]; ring
  refine (integral_le_of_even_dyadic hFi
    (fun t => by
      show ‖dilationSymbol η N b (-t)‖ ^ 2 * criticalSourceWeight η (-t) =
        ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t
      rw [norm_dilationSymbol_neg, criticalSourceWeight_neg])
    hT₁0 ((hsum5.mul_left A).mul_right (∑ k ∈ Finset.range N, b k ^ 2))
    (fun j => by positivity) hlowI (fun j => ?_)).trans ?_
  · have h2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hTT : T₁ ≤ (2 : ℝ) ^ j * T₁ := le_mul_of_one_le_left hT₁0.le h2j
    rw [show (2 : ℝ) ^ (j + 1) * T₁ = 2 * ((2 : ℝ) ^ j * T₁) by rw [pow_succ]; ring]
    refine (integral_weighted_symbol_shell_le h0 h1 hC₂ (fun t ht => (hwη t).2 ht) hb
      (hT₁8.trans hTT) (hT₁T₀.trans hTT) hFi.intervalIntegrable).trans ?_
    rw [hA]
    exact mul_le_mul_of_nonneg_right (dyadic_shell_constant_le hC₂ (by linarith) j) hnb0
  · rw [tsum_mul_right, tsum_mul_left]
    have := mul_le_mul_of_nonneg_right hAK (mul_nonneg hS0 hnb0)
    nlinarith

/-! ### The chain beyond `K` -/

/-- **The tails of the chain are uniformly small for `½ < η < 1`**: for `b` vanishing below `K`,
`Σ_{n<T} (C_η b)(n)² ≤ M K^{−1/10} Σ_k b_k²`. -/
theorem exists_centeredOperator_tail_l2_le_uniform :
    ∃ M K₁ : ℝ, 0 ≤ M ∧ ∀ (η : ℝ) (h0 : 1 / 2 < η), η < 1 → ∀ (b : C₀(ℕ, ℝ)) {N K : ℕ},
      K₁ ≤ K → (∀ k, N ≤ k → b k = 0) → (∀ k, k < K → b k = 0) → ∀ T : ℕ,
        ∑ n ∈ Finset.range T,
            arithmeticDampingCenteredOperator (by linarith : (0 : ℝ) < η) b n ^ 2 ≤
          M * (K : ℝ) ^ (-(1 / 10 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 := by
  obtain ⟨MF, K₁, hMF, hF⟩ := exists_integral_weighted_symbol_tail_le
  refine ⟨8 * (MF / (2 * Real.pi)) + 16, max K₁ 1, by positivity,
    fun η h0 h1 b N K hK hb hlow T => ?_⟩
  have hK1 : (1 : ℝ) ≤ K := (le_max_right _ _).trans hK
  have hK1' : 1 ≤ K := by exact_mod_cast hK1
  have hnb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  obtain ⟨hint, heq⟩ := integral_sq_div_sq_eq_mellin (measurable_combinedProfile η N b) h0
    (fun x hx => (abs_combinedProfile_le_bound h0 h1 N b hx).1)
    (fun x hx => (abs_combinedProfile_le_bound h0 h1 N b hx).2)
  have hnorm : ∀ t : ℝ, ‖mellin (fun x => (combinedProfile η N b x : ℂ))
      (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 =
      ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t := by
    intro t
    rw [mellin_combinedProfile_eq h0 h1 N b t, norm_mul, mul_pow]
    rfl
  have hexp1 : (K : ℝ) ^ (-(7 / 64 : ℝ)) ≤ (K : ℝ) ^ (-(1 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
  have hexp2 : 1 / (K : ℝ) ≤ (K : ℝ) ^ (-(1 / 10 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
  have hG : ∫ x in Ioi (0 : ℝ), combinedProfile η N b x ^ 2 / x ^ 2 ≤
      MF / (2 * Real.pi) * (K : ℝ) ^ (-(1 / 10 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 := by
    rw [heq, funext hnorm]
    have h := hF η h0 h1 N K b ((le_max_left _ _).trans hK) hb hlow
    have h' : MF * (K : ℝ) ^ (-(7 / 64 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 ≤
        MF * (K : ℝ) ^ (-(1 / 10 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp1 hMF) hnb0
    calc 1 / (2 * Real.pi) * ∫ t : ℝ, ‖dilationSymbol η N b t‖ ^ 2 * criticalSourceWeight η t
        ≤ 1 / (2 * Real.pi) * (MF * (K : ℝ) ^ (-(1 / 10 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2) :=
          mul_le_mul_of_nonneg_left (h.trans h') (by positivity)
      _ = _ := by ring
  have hfloor : (∑ k ∈ Finset.range N, |b k| * (1 / ((k + 1 : ℕ) : ℝ))) ^ 2 ≤
      (K : ℝ) ^ (-(1 / 10 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 := by
    refine (sq_sum_abs_div_succ_le_of_vanish hK1' N hlow).trans ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hexp2 hnb0
  refine (sum_sq_centeredOperator_le_integral_add h0 h1 b hb T hint).trans ?_
  have := mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 8)
  have := mul_le_mul_of_nonneg_left hfloor (by norm_num : (0 : ℝ) ≤ 16)
  linarith

/-- **The chain is compact at half damping**: for every finitely supported `b` vanishing below
`K ≥ K₁` and every horizon, `Σ_{n<T} (C_{½} b)(n)² ≤ M K^{−1/10} Σ_k b_k²`. -/
theorem exists_centeredOperator_tail_l2_le_half :
    ∃ M K₁ : ℝ, 0 ≤ M ∧ ∀ (b : C₀(ℕ, ℝ)) {N K : ℕ}, K₁ ≤ K → (∀ k, N ≤ k → b k = 0) →
      (∀ k, k < K → b k = 0) → ∀ T : ℕ,
        ∑ n ∈ Finset.range T,
            arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) b n ^ 2 ≤
          M * (K : ℝ) ^ (-(1 / 10 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 := by
  obtain ⟨M, K₁, hM, hunif⟩ := exists_centeredOperator_tail_l2_le_uniform
  refine ⟨M, K₁, hM, fun b N K hK hb hlow T => ?_⟩
  set φ : ℝ → ℝ := fun η => ∑ n ∈ Finset.range T,
    (∑ k ∈ Finset.range N, arithmeticDampingCenteredRow η n k * b k) ^ 2 with hφ
  have happ : ∀ (η : ℝ) (hη : 0 < η) (n : ℕ), arithmeticDampingCenteredOperator hη b n =
      ∑ k ∈ Finset.range N, arithmeticDampingCenteredRow η n k * b k := by
    intro η hη n
    rw [arithmeticDampingCenteredOperator_apply]
    exact tsum_eq_sum fun k hk => by rw [hb k (by simpa using hk), mul_zero]
  have hcont : ContinuousAt φ (1 / 2) := by
    simp only [hφ]
    refine tendsto_finsetSum _ fun n _ => ?_
    refine ContinuousAt.pow (tendsto_finsetSum _ fun k _ => ?_) 2
    exact (continuousAt_centeredRow n k (by norm_num)).mul continuousAt_const
  have hev : ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ),
      φ η ≤ M * (K : ℝ) ^ (-(1 / 10 : ℝ)) * ∑ k ∈ Finset.range N, b k ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 / 2 : ℝ) < 1)] with η hη
    have h := hunif η hη.1 hη.2 b hK hb hlow T
    simp only [hφ]
    simp only [happ η (by linarith [hη.1])] at h
    exact h
  have hlim := le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  simp only [hφ] at hlim
  simp only [happ (1 / 2) (by norm_num)]
  exact hlim

/-- **`C_{½}` is the operator-norm limit of its finite sections**: for every `ε > 0` there is `K`
with `Σ_{n<T} (C_{½} b)(n)² ≤ ε Σ_k b_k²` for every finitely supported `b` vanishing below `K`. -/
theorem centeredOperator_half_tail_small {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (b : C₀(ℕ, ℝ)) {N : ℕ}, (∀ k, N ≤ k → b k = 0) → (∀ k, k < K → b k = 0) →
      ∀ T : ℕ, ∑ n ∈ Finset.range T,
          arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) b n ^ 2 ≤
        ε * ∑ k ∈ Finset.range N, b k ^ 2 := by
  obtain ⟨M, K₁, hM, h⟩ := exists_centeredOperator_tail_l2_le_half
  have hlim : Tendsto (fun K : ℕ => M * (K : ℝ) ^ (-(1 / 10 : ℝ))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop).const_mul M
    simpa using this
  obtain ⟨K, hK⟩ := ((hlim.eventually (gt_mem_nhds hε)).and
    (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop K₁))).exists
  refine ⟨K, fun b N hb hlow T => (h b hK.2 hb hlow T).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hK.1.le (Finset.sum_nonneg fun k _ => sq_nonneg _)

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
