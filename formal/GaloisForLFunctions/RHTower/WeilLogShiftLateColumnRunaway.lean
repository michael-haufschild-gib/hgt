import GaloisForLFunctions.RHTower.WeilLogShiftSubdiagonalAmplification
import GaloisForLFunctions.RHTower.WeilLogShiftRecoveryColumns

/-!
# Runaway coefficients in every sufficiently late inverse column

The adjacent recovery weight dominates the sum of all older contributions
once their inductive damping is included. A single sufficiently late history
impulse therefore forces sustained coefficient growth, not merely a large
moving diagonal.
-/

open Filter Topology Real
open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

private theorem coefficientColumn_older_tail_bound {J k n : ℕ}
    (hk : J ≤ k)
    (hrow : ∀ j : ℕ, J ≤ j → j + 1 ≤ n →
      ((n : ℝ) + 1) * |weilLogShiftRecoveryWeight (n + 1) j| *
        exp (-((j : ℝ) + 1) * ((n : ℝ) - j)) ≤
          weilLogShiftRecoveryWeight (n + 1) n / 2)
    (hadj : 0 ≤ weilLogShiftRecoveryWeight (n + 1) n)
    (hprev : ∀ j : ℕ, k + 2 ≤ j → j ≤ n →
      exp (((j : ℝ) + 1) * ((n : ℝ) - j)) *
        |weilLogShiftRecoveryCoefficientColumn k j| ≤
          |weilLogShiftRecoveryCoefficientColumn k n|) :
    |∑ j ∈ Finset.Icc 2 (n - 1),
      weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j| ≤
        weilLogShiftRecoveryWeight (n + 1) n *
          |weilLogShiftRecoveryCoefficientColumn k n| / 2 := by
  let B := (weilLogShiftRecoveryWeight (n + 1) n / 2) *
    |weilLogShiftRecoveryCoefficientColumn k n| / ((n : ℝ) + 1)
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 2 (n - 1)) :
      |weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j| ≤ B := by
    have hj' := Finset.mem_Icc.mp hj
    by_cases hseed : k + 2 ≤ j
    · have h := hprev j hseed (by omega)
      let G := ((j : ℝ) + 1) * ((n : ℝ) - j)
      have hcoeff : |weilLogShiftRecoveryCoefficientColumn k j| ≤
          exp (-G) * |weilLogShiftRecoveryCoefficientColumn k n| := by
        calc
          _ = exp (-G) * (exp G * |weilLogShiftRecoveryCoefficientColumn k j|) := by
            rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left h (exp_pos _).le
      have hr := hrow j (by omega) (by omega)
      apply (le_div_iff₀ hN).mpr
      change |weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j| *
        ((n : ℝ) + 1) ≤ _
      calc
        _ = (((n : ℝ) + 1) * |weilLogShiftRecoveryWeight (n + 1) j|) *
            |weilLogShiftRecoveryCoefficientColumn k j| := by rw [abs_mul]; ring
        _ ≤ (((n : ℝ) + 1) * |weilLogShiftRecoveryWeight (n + 1) j|) *
            (exp (-G) * |weilLogShiftRecoveryCoefficientColumn k n|) :=
          mul_le_mul_of_nonneg_left hcoeff (by positivity)
        _ = (((n : ℝ) + 1) * |weilLogShiftRecoveryWeight (n + 1) j| * exp (-G)) *
            |weilLogShiftRecoveryCoefficientColumn k n| := by ring
        _ ≤ _ := by
          simpa only [G, neg_mul] using mul_le_mul_of_nonneg_right hr
            (abs_nonneg (weilLogShiftRecoveryCoefficientColumn k n))
    · rw [weilLogShiftRecoveryCoefficientColumn_eq_zero k j (by omega), zero_mul, abs_zero]
      exact hB
  have hsubset : Finset.Icc 2 (n - 1) ⊆ Finset.range (n + 1) := by
    intro j hj
    have h := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  have hcard : (Finset.Icc 2 (n - 1)).card ≤ n + 1 := by
    simpa only [Finset.card_range] using Finset.card_le_card hsubset
  calc
    _ ≤ ∑ j ∈ Finset.Icc 2 (n - 1),
        |weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Icc 2 (n - 1), B := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 2 (n - 1)).card : ℝ) * B := by simp
    _ ≤ ((n : ℝ) + 1) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
    _ = _ := by dsimp only [B]; field_simp [hN.ne']

/-- Every sufficiently late fixed coefficient column grows by at least the
accumulated exponential factor between any two indices after its seed. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_growth :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ n : ℕ, k + 2 ≤ n →
      ∀ j : ℕ, k + 2 ≤ j → j ≤ n →
        exp (((j : ℝ) + 1) * ((n : ℝ) - j)) *
          |weilLogShiftRecoveryCoefficientColumn k j| ≤
            |weilLogShiftRecoveryCoefficientColumn k n| := by
  obtain ⟨J, hJ, htail⟩ := exists_weilLogShiftRecoveryWeight_tail_dominance_threshold
  obtain ⟨M, hM⟩ := eventually_atTop.mp eventually_weilLogShiftRecoveryWeight_subdiagonal_amplifies
  let K := max J M
  refine ⟨K, hJ.trans (le_max_left _ _), fun k hk => ?_⟩
  have hkJ : J ≤ k := (le_max_left _ _).trans hk
  have hkM : M ≤ k := (le_max_right _ _).trans hk
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro j hj hj'
      have heq : j = k + 2 := by omega
      subst j
      simp only [sub_self, mul_zero, exp_zero, one_mul, le_refl]
  | succ n hn ih =>
      have hdiag := weilLogShiftRecoveryWeight_diagonal_pos (n + 1) (by omega)
      have hamp := hM n (by omega)
      have hadj : 0 < weilLogShiftRecoveryWeight (n + 1) n :=
        (mul_pos (mul_pos (by norm_num) (exp_pos _)) hdiag).trans_le hamp
      have hsum := coefficientColumn_older_tail_bound hkJ
        (fun j hj hjn => htail n j (by omega) hj hjn) hadj.le ih
      have hrec := weilLogShiftRecoveryCoefficientColumn_row_zero k (n + 1) (by omega)
      rw [Finset.sum_Icc_succ_top (by omega)] at hrec
      have hsplit : (∑ j ∈ Finset.Icc 2 n,
          weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j) =
          (∑ j ∈ Finset.Icc 2 (n - 1),
            weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j) +
          weilLogShiftRecoveryCoefficientColumn k n * weilLogShiftRecoveryWeight (n + 1) n := by
        have h := Finset.sum_Icc_succ_top (a := 2) (b := n - 1) (by omega)
          (fun j => weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j)
        simpa only [show n - 1 + 1 = n by omega] using h
      rw [hsplit] at hrec
      have heq : weilLogShiftRecoveryCoefficientColumn k n * weilLogShiftRecoveryWeight (n + 1) n =
          -(weilLogShiftRecoveryCoefficientColumn k (n + 1) * weilLogShiftRecoveryWeight (n + 1) (n + 1) +
            ∑ j ∈ Finset.Icc 2 (n - 1),
              weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j) := by
        linarith only [hrec]
      have htri := abs_add_le
        (weilLogShiftRecoveryCoefficientColumn k (n + 1) * weilLogShiftRecoveryWeight (n + 1) (n + 1))
        (∑ j ∈ Finset.Icc 2 (n - 1),
          weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j)
      rw [← abs_neg, ← heq, abs_mul, abs_mul, abs_of_pos hadj, abs_of_pos hdiag] at htri
      have hamp' := mul_le_mul_of_nonneg_right hamp
        (abs_nonneg (weilLogShiftRecoveryCoefficientColumn k n))
      have hstep : exp ((n : ℝ) + 1) * |weilLogShiftRecoveryCoefficientColumn k n| ≤
          |weilLogShiftRecoveryCoefficientColumn k (n + 1)| := by
        apply (mul_le_mul_iff_left₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hdiag)).mp
        nlinarith only [htri, hsum, hamp']
      intro j hj hjn
      by_cases hlast : j = n + 1
      · subst j
        simp only [sub_self, mul_zero, exp_zero, one_mul, le_refl]
      · have hjn' : j ≤ n := by omega
        have hjnR : (j : ℝ) ≤ n := by exact_mod_cast hjn'
        have hprev := ih j hj hjn'
        have he : exp (((j : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) - j)) =
            exp ((j : ℝ) + 1) * exp (((j : ℝ) + 1) * ((n : ℝ) - j)) := by
          rw [← exp_add]
          congr 1
          push_cast
          ring
        rw [he, mul_assoc]
        calc
          _ ≤ exp ((n : ℝ) + 1) * (exp (((j : ℝ) + 1) * ((n : ℝ) - j)) *
              |weilLogShiftRecoveryCoefficientColumn k j|) :=
            mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith only [hjnR])) (by positivity)
          _ ≤ exp ((n : ℝ) + 1) * |weilLogShiftRecoveryCoefficientColumn k n| :=
            mul_le_mul_of_nonneg_left hprev (exp_pos _).le
          _ ≤ _ := hstep

/-- Uniform native half-tail control, including strict positivity of the
adjacent weight and nonvanishing of the current column coefficient. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_older_tail_half_bound :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∀ n : ℕ, k + 2 ≤ n →
      0 < weilLogShiftRecoveryWeight (n + 1) n ∧
      0 < |weilLogShiftRecoveryCoefficientColumn k n| ∧
      |∑ j ∈ Finset.Icc 2 (n - 1),
        weilLogShiftRecoveryCoefficientColumn k j * weilLogShiftRecoveryWeight (n + 1) j| ≤
        weilLogShiftRecoveryWeight (n + 1) n *
          |weilLogShiftRecoveryCoefficientColumn k n| / 2 := by
  obtain ⟨J, hJ, htail⟩ := exists_weilLogShiftRecoveryWeight_tail_dominance_threshold
  obtain ⟨M, hM⟩ := eventually_atTop.mp eventually_weilLogShiftRecoveryWeight_subdiagonal_amplifies
  obtain ⟨G, _, hgrowth⟩ := exists_weilLogShiftRecoveryCoefficientColumn_growth
  refine ⟨max (max J M) G, by omega, ?_⟩
  intro k hk n hn
  have hdiag := weilLogShiftRecoveryWeight_diagonal_pos (n + 1) (by omega)
  have hamp := hM n (by omega)
  have hadj : 0 < weilLogShiftRecoveryWeight (n + 1) n :=
    (mul_pos (mul_pos (by norm_num) (exp_pos _)) hdiag).trans_le hamp
  have hprev := hgrowth k (by omega) n hn
  have hseed := hprev (k + 2) le_rfl hn
  have hnonzero : 0 < |weilLogShiftRecoveryCoefficientColumn k n| :=
    (mul_pos (exp_pos _) (abs_pos.mpr
      (weilLogShiftRecoveryCoefficientColumn_seed_pos k).ne')).trans_le hseed
  exact ⟨hadj, hnonzero, coefficientColumn_older_tail_bound (by omega)
    (fun j hj hjn => htail n j (by omega) hj hjn) hadj.le hprev⟩

/-- Each sufficiently late column has a positive exponential lower envelope
whose rate is its seed index plus one. -/
theorem exists_weilLogShiftRecoveryCoefficientColumn_exponential_lower :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ k : ℕ, K ≤ k → ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, k + 2 ≤ n →
        c * exp (((k : ℝ) + 3) * n) ≤ |weilLogShiftRecoveryCoefficientColumn k n| := by
  obtain ⟨K, hK, hgrowth⟩ := exists_weilLogShiftRecoveryCoefficientColumn_growth
  refine ⟨K, hK, fun k hk => ?_⟩
  let c := |weilLogShiftRecoveryCoefficientColumn k (k + 2)| *
    exp (-(((k : ℝ) + 3) * ((k : ℝ) + 2)))
  have hc : 0 < c := mul_pos
    (abs_pos.mpr (weilLogShiftRecoveryCoefficientColumn_seed_pos k).ne') (exp_pos _)
  refine ⟨c, hc, fun n hn => ?_⟩
  have h := hgrowth k hk n hn (k + 2) le_rfl hn
  calc
    _ = exp (((((k + 2 : ℕ) : ℝ)) + 1) * ((n : ℝ) - (k + 2 : ℕ))) *
        |weilLogShiftRecoveryCoefficientColumn k (k + 2)| := by
      dsimp only [c]
      rw [mul_assoc, ← exp_add]
      have he : -(((k : ℝ) + 3) * ((k : ℝ) + 2)) + ((k : ℝ) + 3) * n =
          ((((k + 2 : ℕ) : ℝ)) + 1) * ((n : ℝ) - (k + 2 : ℕ)) := by push_cast; ring
      rw [he, mul_comm]
    _ ≤ _ := h

/-- A sufficiently late error in one fixed history coordinate makes the
absolute response terms tend to infinity at every real shift. -/
theorem exists_weilLogShiftRecoveryMomentResponse_fixed_column_runaway :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ y : ℝ,
      Tendsto (fun n : ℕ => |weilLogShiftRecoveryMomentResponse y n k|) atTop atTop := by
  obtain ⟨K, hK, hcoeff⟩ := exists_weilLogShiftRecoveryCoefficientColumn_exponential_lower
  refine ⟨K, fun k hk y => ?_⟩
  obtain ⟨c, hc, hcoef⟩ := hcoeff k hk
  have hkR : (625 : ℝ) ≤ k := by exact_mod_cast hK.trans hk
  have hrate : logKernelCriticalRate y < 2 * π + 1 := by
    have he : exp (-|y|) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg y))
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * π by positivity)
    dsimp only [logKernelCriticalRate]
    linarith only [h]
  obtain ⟨D, hD, hkernel⟩ := exists_paired_logKernel_lower_of_rate_lt hrate
  let γ := (k : ℝ) + 3 - (2 * π + 1)
  let A := c * D
  have hγ : 0 < γ := by dsimp only [γ]; linarith only [hkR, pi_lt_four]
  have hA : 0 < A := mul_pos hc hD
  have hlower : ∀ᶠ n : ℕ in atTop,
      (A / ((n : ℝ) + 1)) * exp (γ * n) ≤
        |weilLogShiftRecoveryMomentResponse y n k| := by
    filter_upwards [hkernel, eventually_ge_atTop (k + 2)] with n hker hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hN : 0 < (n : ℝ) + 1 := by positivity
    have hsqrt : 0 < sqrt (n : ℝ) := sqrt_pos.mpr hnpos
    have hsqrtN : sqrt (n : ℝ) ≤ (n : ℝ) + 1 := by
      have h := sqrt_le_self_iff.mpr (Or.inr (show (1 : ℝ) ≤ n by
        exact_mod_cast (show 1 ≤ n by omega)))
      linarith only [h]
    have hcn := hcoef n hn
    change D * exp (-((2 * π + 1) * n)) ≤ pairedLogKernel y n at hker
    rw [weilLogShiftRecoveryMomentResponse_eq_coefficientColumn y k n (by omega),
      abs_mul, abs_div, abs_of_pos hsqrt, abs_of_pos (pairedLogKernel_pos y n)]
    calc
      _ = ((c * exp (((k : ℝ) + 3) * n)) / ((n : ℝ) + 1)) *
          (D * exp (-((2 * π + 1) * n))) := by
        have he : exp (γ * n) = exp (((k : ℝ) + 3) * n) *
            exp (-((2 * π + 1) * n)) := by
          rw [← exp_add]
          congr 1
          dsimp only [γ]
          ring
        rw [he]
        dsimp only [A]
        ring
      _ ≤ (|weilLogShiftRecoveryCoefficientColumn k n| / ((n : ℝ) + 1)) *
          pairedLogKernel y n := mul_le_mul
        (div_le_div_of_nonneg_right hcn hN.le) hker (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (abs_nonneg _) hsqrt hsqrtN) (pairedLogKernel_pos y n).le
  have hx : Tendsto (fun n : ℕ => γ * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hγ
  have hsmall : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * exp (-(γ * n))) atTop (𝓝 0) := by
    have h₁ := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx).const_mul (1 / γ)
    have h₂ := tendsto_exp_neg_atTop_nhds_zero.comp hx
    convert h₁.add h₂ using 1
    · funext n
      simp only [Function.comp_def, pow_one]
      field_simp [hγ.ne']
    · simp only [mul_zero, add_zero]
  apply tendsto_atTop.mpr
  intro B
  have hBsmall := hsmall.const_mul |B|
  rw [mul_zero] at hBsmall
  filter_upwards [hlower, (tendsto_order.mp hBsmall).2 A hA] with n hn hs
  have hscaled : |B| * ((n : ℝ) + 1) ≤ A * exp (γ * n) := by
    calc
      _ = (|B| * (((n : ℝ) + 1) * exp (-(γ * n)))) * exp (γ * n) := by
        rw [mul_assoc |B|, mul_assoc ((n : ℝ) + 1), ← exp_add, neg_add_cancel,
          exp_zero, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hs.le (exp_pos _).le
  calc
    B ≤ |B| := le_abs_self B
    _ ≤ (A * exp (γ * n)) / ((n : ℝ) + 1) :=
      (le_div_iff₀ (by positivity)).mpr hscaled
    _ = (A / ((n : ℝ) + 1)) * exp (γ * n) := by ring
    _ ≤ _ := hn

/-- Every sufficiently late fixed impulse column is nonsummable at every
real shift, independently of any envelope imposed on later history errors. -/
theorem exists_weilLogShiftRecoveryMomentResponse_fixed_column_not_summable :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ y : ℝ,
      ¬ Summable (fun n : ℕ => weilLogShiftRecoveryMomentResponse y n k) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftRecoveryMomentResponse_fixed_column_runaway
  refine ⟨K, fun k hk y hs => ?_⟩
  have hzero : Tendsto (fun n : ℕ => |weilLogShiftRecoveryMomentResponse y n k|)
      atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using hs.norm.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((hK k hk y).eventually_ge_atTop 1).and ((tendsto_order.mp hzero).2 1 (by norm_num)))
  have hn := hN N le_rfl
  linarith only [hn.1, hn.2]

end RHTower
