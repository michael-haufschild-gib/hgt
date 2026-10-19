import GaloisForLFunctions.RHTower.QuasiRHMeanSquareAbscissa

/-!
# The paid dilation diagonal and the remaining signed covariance

The normalized high-dilation diagonal costs at most `9 / 25` at each scale. Its cumulative
cost is therefore linear. The off-diagonal is kept as the literal ordered pair sum, with
both Möbius signs retained. Its upper growth determines the zero abscissa once the explicit
head cost is paid; no improved bound for the off-diagonal is assumed or asserted here.
-/

open Real Filter Topology Finset
open scoped BigOperators

namespace RHTower

/-- The normalized diagonal of the actual high-dilation square. -/
noncomputable def mobiusDivisorDilationTailDiagonal (M D : ℕ) : ℝ :=
  (∑ d ∈ Icc (D + 1) (M - 1), (mobiusDivisorDilationChannel M d) ^ 2) / (M : ℝ) ^ 2

/-- Ordered pairs of distinct high dilations, with their original signs. -/
noncomputable def mobiusDivisorDilationTailCovariance (M D : ℕ) : ℝ :=
  (∑ d ∈ Icc (D + 1) (M - 1), ∑ e ∈ (Icc (D + 1) (M - 1)).erase d,
    mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e) / (M : ℝ) ^ 2

/-- Exact diagonal/off-diagonal decomposition; ordered pairs require no factor of two. -/
theorem mobiusDivisorDilationTail_sq_eq_diagonal_add_covariance (M D : ℕ) :
    (mobiusDivisorDilationTail M D / M) ^ 2 =
      mobiusDivisorDilationTailDiagonal M D + mobiusDivisorDilationTailCovariance M D := by
  unfold mobiusDivisorDilationTail mobiusDivisorDilationTailDiagonal mobiusDivisorDilationTailCovariance
  rw [div_pow, ← add_div]
  congr 1
  rw [pow_two, sum_mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [← sum_erase_add _ (fun e => mobiusDivisorDilationChannel M d * mobiusDivisorDilationChannel M e) hd]
  ring

/-- The literal diagonal has a scale-independent normalized ceiling. -/
theorem mobiusDivisorDilationTailDiagonal_bounds {M : ℕ} (hM : 1 ≤ M) (D : ℕ) :
    0 ≤ mobiusDivisorDilationTailDiagonal M D ∧ mobiusDivisorDilationTailDiagonal M D ≤ 9 / 25 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hterm (d : ℕ) : (mobiusDivisorDilationChannel M d) ^ 2 ≤ (9 / 25 : ℝ) * M := by
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (3 / 5 : ℝ) * Real.sqrt M)).mpr
      (abs_mobiusDivisorDilationChannel_le_three_fifths_sqrt M d)
    rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg M)] at hs
    norm_num at hs ⊢
    exact hs
  have hsum : ∑ d ∈ Icc (D + 1) (M - 1), (mobiusDivisorDilationChannel M d) ^ 2 ≤
      (9 / 25 : ℝ) * (M : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _d ∈ Icc (D + 1) (M - 1), (9 / 25 : ℝ) * M := sum_le_sum fun d _ => hterm d
      _ = ((Icc (D + 1) (M - 1)).card : ℝ) * ((9 / 25 : ℝ) * M) := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * ((9 / 25 : ℝ) * M) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (show (Icc (D + 1) (M - 1)).card ≤ M by rw [Nat.card_Icc]; omega)
      _ = _ := by ring
  constructor
  · unfold mobiusDivisorDilationTailDiagonal; positivity
  · exact (div_le_iff₀ (sq_pos_of_pos hM0)).mpr hsum

/-- Cumulative signed covariance above the moving power cutoff. -/
noncomputable def mobiusDivisorDilationCovariancePrefix (φ : ℝ) (N : ℕ) : ℝ :=
  ∑ M ∈ Icc 2 N, mobiusDivisorDilationTailCovariance M ⌊(M : ℝ) ^ φ⌋₊

/-- The difference between cumulative tail energy and covariance is nonnegative and linear. -/
theorem mobiusDivisorDilationTailMeanSquareEnergy_sub_covariance_bounds (φ : ℝ) (N : ℕ) :
    0 ≤ mobiusDivisorDilationTailMeanSquareEnergy φ N - mobiusDivisorDilationCovariancePrefix φ N ∧
    mobiusDivisorDilationTailMeanSquareEnergy φ N - mobiusDivisorDilationCovariancePrefix φ N ≤
      (9 / 25 : ℝ) * N := by
  have hid : mobiusDivisorDilationTailMeanSquareEnergy φ N - mobiusDivisorDilationCovariancePrefix φ N =
      ∑ M ∈ Icc 2 N, mobiusDivisorDilationTailDiagonal M ⌊(M : ℝ) ^ φ⌋₊ := by
    unfold mobiusDivisorDilationTailMeanSquareEnergy mobiusDivisorDilationCovariancePrefix
    simp_rw [mobiusDivisorDilationTail_sq_eq_diagonal_add_covariance]
    rw [sum_add_distrib, add_sub_cancel_right]
  rw [hid]
  constructor
  · exact sum_nonneg fun M hM => (mobiusDivisorDilationTailDiagonal_bounds
      (by have := (mem_Icc.mp hM).1; omega) _).1
  · calc
      _ ≤ ∑ _M ∈ Icc 2 N, (9 / 25 : ℝ) := sum_le_sum fun M hM =>
        (mobiusDivisorDilationTailDiagonal_bounds (by have := (mem_Icc.mp hM).1; omega) _).2
      _ = ((Icc 2 N).card : ℝ) * (9 / 25 : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        have hcard : ((Icc 2 N).card : ℝ) ≤ N := by
          exact_mod_cast (show (Icc 2 N).card ≤ N by rw [Nat.card_Icc]; omega)
        linarith

/-- Cancellation cannot make the cumulative covariance more negative than its paid diagonal. -/
theorem neg_linear_le_mobiusDivisorDilationCovariancePrefix (φ : ℝ) (N : ℕ) :
    -(9 / 25 : ℝ) * N ≤ mobiusDivisorDilationCovariancePrefix φ N := by
  have h := (mobiusDivisorDilationTailMeanSquareEnergy_sub_covariance_bounds φ N).2
  have hnonneg : 0 ≤ mobiusDivisorDilationTailMeanSquareEnergy φ N := by
    unfold mobiusDivisorDilationTailMeanSquareEnergy; positivity
  linarith

/-- A one-sided covariance bound pays the entire mean-square route once the head fits. -/
theorem zetaZeroAbscissa_le_half_of_mobiusDivisorDilationCovariancePrefix_le_rpow
    {φ C r : ℝ} (hφ : 1 / 2 ≤ φ) (hr : 2 * φ ≤ r) (hC : 0 ≤ C)
    (hV : ∀ N : ℕ, 2 ≤ N → mobiusDivisorDilationCovariancePrefix φ N ≤ C * (N : ℝ) ^ r) :
    zetaZeroAbscissa ≤ r / 2 := by
  have hr1 : 1 ≤ r := by linarith
  apply zetaZeroAbscissa_le_half_of_mobiusDivisorAbelMeanSquareEnergy_le_rpow
    (C := 2 * C + 36 / 25) (by positivity) hr1
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hpN : (N : ℝ) ≤ (N : ℝ) ^ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hr1
  have hhead : (N : ℝ) ^ (2 * φ) ≤ (N : ℝ) ^ r := Real.rpow_le_rpow_of_exponent_le hN1 hr
  have hsplit := (mobiusDivisorDilationTailMeanSquareEnergy_comparison hφ hN).1
  have hdiag := (mobiusDivisorDilationTailMeanSquareEnergy_sub_covariance_bounds φ N).2
  have hcov := hV N hN
  nlinarith

/-- The exact endpoint criterion retains only the signed off-diagonal arithmetic estimate. -/
theorem zetaZeroAbscissa_le_iff_mobiusDivisorDilationCovariancePrefix_subpower
    {φ b : ℝ} (hφ : 1 / 2 ≤ φ) (hb : φ ≤ b) :
    zetaZeroAbscissa ≤ b ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 2 ≤ N → mobiusDivisorDilationCovariancePrefix φ N ≤ C * (N : ℝ) ^ (2 * b + ε) := by
  constructor
  · intro hstrip ε hε
    obtain ⟨C, hC, hbound⟩ := exists_mobiusDivisorAbelMeanSquareEnergy_le_rpow_zetaZeroAbscissa ε hε
    refine ⟨2 * C + 18 / 25, by positivity, fun N hN => ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hpower : (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) ≤ (N : ℝ) ^ (2 * b + ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hE := (hbound N hN).trans (mul_le_mul_of_nonneg_left hpower hC)
    have hhead : (N : ℝ) ^ (2 * φ) ≤ (N : ℝ) ^ (2 * b + ε) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hsplit := (mobiusDivisorDilationTailMeanSquareEnergy_comparison hφ hN).2
    have hdiag := (mobiusDivisorDilationTailMeanSquareEnergy_sub_covariance_bounds φ N).1
    nlinarith
  · intro hV
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, hC, hbound⟩ := hV (2 * ε) (by positivity)
    have := zetaZeroAbscissa_le_half_of_mobiusDivisorDilationCovariancePrefix_le_rpow
      hφ (by linarith : 2 * φ ≤ 2 * b + 2 * ε) hC hbound
    linarith

/-- At the square-root cutoff, signed covariance has the same exact exponent as the full energy. -/
theorem two_mul_zetaZeroAbscissa_eq_sInf_dilationCovariance_half_exponents :
    2 * zetaZeroAbscissa = sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 2 ≤ N → mobiusDivisorDilationCovariancePrefix (1 / 2) N ≤ C * (N : ℝ) ^ r} := by
  let S : Set ℝ := {r | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 2 ≤ N → mobiusDivisorDilationCovariancePrefix (1 / 2) N ≤ C * (N : ℝ) ^ r}
  have hmem : ∀ ε : ℝ, 0 < ε → 2 * zetaZeroAbscissa + ε ∈ S := by
    intro ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa],
      (zetaZeroAbscissa_le_iff_mobiusDivisorDilationCovariancePrefix_subpower
        (φ := 1 / 2) (by norm_num) half_le_zetaZeroAbscissa).mp le_rfl ε hε⟩
  have hne : S.Nonempty := ⟨2 * zetaZeroAbscissa + 1, hmem 1 (by norm_num)⟩
  have hbdd : BddBelow S := ⟨1, fun _ hr => hr.1⟩
  change 2 * zetaZeroAbscissa = sInf S
  apply le_antisymm
  · refine le_csInf hne fun r hr => ?_
    obtain ⟨hr, C, hC, hV⟩ := hr
    have := zetaZeroAbscissa_le_half_of_mobiusDivisorDilationCovariancePrefix_le_rpow
      (φ := 1 / 2) (by norm_num) (by linarith) hC hV
    linarith
  · exact le_of_forall_pos_le_add fun ε hε => csInf_le hbdd (hmem ε hε)

/-- The `5/6` route is exactly the displayed one-sided ordered-pair estimate. -/
theorem xi_zero_five_sixths_strip_iff_dilationCovariance_subpower :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 6 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 5 / 6) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        mobiusDivisorDilationCovariancePrefix (5 / 6) N ≤ C * (N : ℝ) ^ (5 / 3 + ε) := by
  rw [← zetaZeroAbscissa_le_five_sixths_iff_xi_zero_mem_strip]
  convert zetaZeroAbscissa_le_iff_mobiusDivisorDilationCovariancePrefix_subpower
    (φ := 5 / 6) (b := 5 / 6) (by norm_num) le_rfl using 1
  norm_num

/-- The `3/4` route is exactly the displayed one-sided ordered-pair estimate. -/
theorem xi_zero_three_quarters_strip_iff_dilationCovariance_subpower :
    (∀ ρ : ℂ, xi ρ = 0 → (1 / 4 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 3 / 4) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
        mobiusDivisorDilationCovariancePrefix (3 / 4) N ≤ C * (N : ℝ) ^ (3 / 2 + ε) := by
  rw [← zetaZeroAbscissa_le_three_quarters_iff_xi_zero_mem_strip]
  convert zetaZeroAbscissa_le_iff_mobiusDivisorDilationCovariancePrefix_subpower
    (φ := 3 / 4) (b := 3 / 4) (by norm_num) le_rfl using 1
  norm_num

end RHTower
