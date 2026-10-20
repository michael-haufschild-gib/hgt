import GaloisForLFunctions.BezoutValuationIncidence.PolynomialWindowTranslatedMomentTransfer
import GaloisForLFunctions.BezoutValuationIncidence.RenormalizedMobiusDefectAndFirstOctaveCancellation
import GaloisForLFunctions.BezoutValuationIncidence.QuadraticWindowHorizonSharpnessAtCommonReturns

/-!
# The degree-`m` transfer horizon is `N^m`

A degree-`m` transfer constant at level `N` is a number `S` such that every degree-`m` translated
window moment, at every phase and length, is within `S Q_Sel(c)^{m/2}` of `K` times its
complete-period value. The window transfer law shows that `S_N^{m/2}` is one, so
`S ≤ ((27/4) N² (1 + log N))^{m/2}` suffices.

Conversely, the top-band row `c = 1_{(N/2, N]}` has period mean square `Q_Sel ≤ H_N³` while its
response at the common return `N!` equals the band size `M₀ = N - ⌊N/2⌋ ≥ N/2`; its period
`m`-th moment is at most `M₀^{m-2} Q_Sel`. A single window sample at `N!` forces
`M₀^m - H_N³ M₀^{m-2} ≤ S (√(H_N³))^m`. Hence every degree-`m` transfer constant is
`N^{m - o(1)}`: observations of degree `m` reach their period values only on windows of length
`N^{m ± o(1)}`. Degree-two transfer is quadratic, the sixth-moment observation protocols of the
arithmetic observation theory need windows of length `N^{6 - o(1)}`, and no moment-transfer
argument reaches a linear horizon.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- `S` transfers every degree-`m` translated moment from windows to the complete period. -/
def IsTranslatedMomentTransferConstant (N m : ℕ) (S : ℝ) : Prop :=
  ∀ (c : ℕ → ℝ) (h : Fin m → ℕ) (A K : ℕ),
    |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + h i)) -
        (K : ℝ) * SieveMoments.translatedMoment N c h| ≤
      S * Real.sqrt (selbergTotientDiagonalForm N c) ^ m

/-- The window observability constant gives the degree-`m` transfer constant `S_N^{m/2}`. -/
theorem isTranslatedMomentTransferConstant_observability (N m : ℕ) :
    IsTranslatedMomentTransferConstant N m (Real.sqrt (sieveWindowObservabilityConstant N) ^ m) :=
  fun c h A K => by
    have h1 := abs_window_translatedMoment_sub_le_observabilityConstant N c h A K
    rwa [Real.sqrt_mul (sieveWindowObservabilityConstant_nonneg N), mul_pow] at h1

/-! ## The top-band row -/

/-- The indicator of the top band `(N/2, N]`. -/
def sieveTopBandRow (N : ℕ) : ℕ → ℝ := fun d => if N / 2 < d then 1 else 0

private theorem sieveSeq_sieveTopBandRow_nonneg (N k : ℕ) : 0 ≤ sieveSeq N (sieveTopBandRow N) k :=
  sum_nonneg fun d _ => by unfold sieveTopBandRow; split_ifs <;> norm_num

private theorem sieveSeq_sieveTopBandRow_le (N k : ℕ) :
    sieveSeq N (sieveTopBandRow N) k ≤ (N - N / 2 : ℕ) := by
  unfold sieveSeq sieveTopBandRow
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have hsub : ((Icc 1 N).filter (fun d => d ∣ k)).filter (fun d => N / 2 < d) ⊆ Ioc (N / 2) N := by
    intro d hd
    simp only [mem_filter, mem_Icc, mem_Ioc] at hd ⊢
    exact ⟨hd.2, hd.1.1.2⟩
  have := card_le_card hsub
  rw [Nat.card_Ioc] at this
  exact_mod_cast this

/-- At the common return `N!` the response is the band size. -/
theorem sieveSeq_sieveTopBandRow_factorial (N : ℕ) :
    sieveSeq N (sieveTopBandRow N) N.factorial = (N - N / 2 : ℕ) := by
  unfold sieveSeq sieveTopBandRow
  rw [filter_true_of_mem fun d hd => Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2,
    sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have hset : (Icc 1 N).filter (fun d => N / 2 < d) = Ioc (N / 2) N := by
    ext d
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  rw [hset, Nat.card_Ioc]

/-- The top-band row lies below the all-ones row, so its period mean square is at most `H_N³`. -/
theorem selbergTotientDiagonalForm_sieveTopBandRow_le (N : ℕ) :
    selbergTotientDiagonalForm N (sieveTopBandRow N) ≤ (harmonic N : ℝ) ^ 3 := by
  refine le_trans ?_ (selbergTotientDiagonalForm_sieveOnesRow_le N)
  unfold selbergTotientDiagonalForm
  refine sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hY0 : 0 ≤ selbergMultiplesCoord N (sieveTopBandRow N) e := by
    unfold selbergMultiplesCoord sieveTopBandRow
    exact sum_nonneg fun d _ => by split_ifs <;> positivity
  refine pow_le_pow_left₀ hY0 ?_ 2
  unfold selbergMultiplesCoord sieveTopBandRow sieveOnesRow
  exact sum_le_sum fun d _ => by
    split_ifs
    · exact le_rfl
    · rw [zero_div]
      exact div_nonneg zero_le_one (Nat.cast_nonneg d)

/-- The complete-period `m`-th moment of the top-band row is at most `M₀^{m-2} Q_Sel`. -/
theorem translatedMoment_sieveTopBandRow_zero_le (N m : ℕ) (hm : 2 ≤ m) :
    SieveMoments.translatedMoment N (sieveTopBandRow N) (fun _ : Fin m => 0) ≤
      ((N - N / 2 : ℕ) : ℝ) ^ (m - 2) * selbergTotientDiagonalForm N (sieveTopBandRow N) := by
  rw [translatedMoment_eq_Icc]
  have hP : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hP]
  have hsq := sum_sieveSeq_sq_eq_selberg_sub_signedLcmFractDefect N N.factorial (sieveTopBandRow N)
  rw [signedLcmFractDefect_eq_zero_of_common_return _ fun d hd =>
    Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2, sub_zero] at hsq
  have hpt : ∀ k ∈ Icc 1 N.factorial, (∏ _i : Fin m, sieveSeq N (sieveTopBandRow N) (k + 0)) ≤
      ((N - N / 2 : ℕ) : ℝ) ^ (m - 2) * sieveSeq N (sieveTopBandRow N) k ^ 2 := by
    intro k _
    rw [prod_const, card_univ, Fintype.card_fin, add_zero]
    have h0 := sieveSeq_sieveTopBandRow_nonneg N k
    have h1 := sieveSeq_sieveTopBandRow_le N k
    calc sieveSeq N (sieveTopBandRow N) k ^ m
        = sieveSeq N (sieveTopBandRow N) k ^ (m - 2) * sieveSeq N (sieveTopBandRow N) k ^ 2 := by
          rw [← pow_add, Nat.sub_add_cancel hm]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 _) (sq_nonneg _)
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, hsq]
  apply le_of_eq
  ring

/-- **Sharpness of the degree-`m` transfer.** Every degree-`m` transfer constant at level `N`
satisfies `M₀^m - H_N³ M₀^{m-2} ≤ S (√(H_N³))^m`, with `M₀ = N - ⌊N/2⌋ ≥ N/2`. -/
theorem isTranslatedMomentTransferConstant_lower_bound {N m : ℕ} (hm : 2 ≤ m) {S : ℝ}
    (hS : IsTranslatedMomentTransferConstant N m S) :
    ((N - N / 2 : ℕ) : ℝ) ^ m - (harmonic N : ℝ) ^ 3 * ((N - N / 2 : ℕ) : ℝ) ^ (m - 2) ≤
      S * Real.sqrt ((harmonic N : ℝ) ^ 3) ^ m := by
  have hH0 : (0 : ℝ) ≤ harmonic N := by
    rw [_root_.harmonic_eq_sum_Icc]
    push_cast
    exact sum_nonneg fun i _ => by positivity
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hm0 : m ≠ 0 := by omega
    simp [zero_pow hm0]
  -- `S ≥ 0` from the constant response `1`
  have hS0 : 0 ≤ S := by
    set u : ℕ → ℝ := fun d => if d = 1 then 1 else 0 with hu
    have hs1 : ∀ k, sieveSeq N u k = 1 := fun k => by
      have hmem : (1 : ℕ) ∈ (Icc 1 N).filter (fun d => d ∣ k) :=
        mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hN⟩, one_dvd k⟩
      unfold sieveSeq
      simp only [hu]
      rw [sum_ite_eq']
      simp [hmem]
    have hT : SieveMoments.translatedMoment N u (fun _ : Fin m => 0) = 1 := by
      unfold SieveMoments.translatedMoment
      simp only [hs1, prod_const_one, sum_const, card_range, nsmul_eq_mul, mul_one]
      exact div_self (by exact_mod_cast (Nat.factorial_pos N).ne')
    have hH : finiteHarmonicSum N u = 1 := by
      unfold finiteHarmonicSum
      rw [hu]
      simp only [ite_div, one_div, zero_div]
      rw [sum_ite_eq' _ 1, if_pos (mem_Icc.mpr ⟨le_rfl, hN⟩)]
      simp
    have hQ1 : 1 ≤ selbergTotientDiagonalForm N u := by
      rw [selberg_eq_harmonic_sq_add_variance, hH]
      have : 0 ≤ sieveVariance N u :=
        sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      linarith
    have h1 := hS u (fun _ => 0) 0 1
    rw [hT] at h1
    simp only [zero_add, Icc_self, sum_singleton, hs1, prod_const_one, Nat.cast_one, mul_one,
      sub_self, abs_zero] at h1
    have hpos : 0 < Real.sqrt (selbergTotientDiagonalForm N u) ^ m :=
      pow_pos (Real.sqrt_pos.mpr (by linarith)) m
    by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hpos]
  have h := hS (sieveTopBandRow N) (fun _ => 0) (N.factorial - 1) 1
  have hP1 : N.factorial - 1 + 1 = N.factorial := Nat.sub_add_cancel (Nat.factorial_pos N)
  rw [hP1, Icc_self, sum_singleton] at h
  simp only [add_zero, prod_const, card_univ, Fintype.card_fin, Nat.cast_one, one_mul,
    sieveSeq_sieveTopBandRow_factorial] at h
  have hT := translatedMoment_sieveTopBandRow_zero_le N m hm
  have hQ := selbergTotientDiagonalForm_sieveTopBandRow_le N
  have hQ0 := selbergTotientDiagonalForm_nonneg N (sieveTopBandRow N)
  have hM0 : (0 : ℝ) ≤ ((N - N / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpow : Real.sqrt (selbergTotientDiagonalForm N (sieveTopBandRow N)) ^ m ≤
      Real.sqrt ((harmonic N : ℝ) ^ 3) ^ m :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hQ) m
  rw [abs_le] at h
  have hTb : SieveMoments.translatedMoment N (sieveTopBandRow N) (fun _ : Fin m => 0) ≤
      ((N - N / 2 : ℕ) : ℝ) ^ (m - 2) * (harmonic N : ℝ) ^ 3 :=
    hT.trans (mul_le_mul_of_nonneg_left hQ (pow_nonneg hM0 _))
  nlinarith [h.2, mul_le_mul_of_nonneg_left hpow hS0]

end

end GaloisForLFunctions.BezoutValuationIncidence
