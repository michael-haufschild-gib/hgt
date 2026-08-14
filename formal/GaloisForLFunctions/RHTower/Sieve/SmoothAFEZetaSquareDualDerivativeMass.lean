import GaloisForLFunctions.RHTower.Sieve.DivisorSquareTail
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualTwoSidedDerivativeBound

noncomputable section

namespace RHTower.Sieve

open Complex Set Finset

private theorem derivative_le_low_conductor
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => RHTower.smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        min
          (C * Y ^ (1 / 4 : ℝ) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2))
          (C * (1 + tau) / Y))
    {N m : ℕ} {tau : ℝ} (hN : 4 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N)
    (htau : tau ∈ Set.Icc (N : ℝ) (2 * N)) :
    ‖deriv (fun u : ℝ =>
        RHTower.smoothAFEZetaSquareDualWeight u ((m : ℝ) * N)) tau‖ ≤
      C / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htaupos : 0 < tau := hNpos.trans_le htau.1
  have htau4 : 4 ≤ tau := (by exact_mod_cast hN : (4 : ℝ) ≤ N) |>.trans htau.1
  have hYpos : 0 < (m : ℝ) * N := mul_pos hmpos hNpos
  have hraw := hderiv htau4 hYpos
  have hYle : (m : ℝ) * N ≤ tau ^ 2 := by
    have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
    calc
      (m : ℝ) * N ≤ (N : ℝ) * N :=
        mul_le_mul_of_nonneg_right hmNR hNpos.le
      _ = (N : ℝ) ^ 2 := by ring
      _ ≤ tau ^ 2 := pow_le_pow_left₀ hNpos.le htau.1 2
  have hquarter : ((m : ℝ) * N) ^ (1 / 4 : ℝ) ≤
      (tau ^ (1 / 4 : ℝ)) ^ 2 := by
    calc
      ((m : ℝ) * N) ^ (1 / 4 : ℝ)
          ≤ (tau ^ 2) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow hYpos.le hYle (by norm_num)
      _ = (tau ^ (1 / 4 : ℝ)) ^ 2 := by
        calc
          (tau ^ 2) ^ (1 / 4 : ℝ) = tau ^ ((2 : ℝ) * (1 / 4 : ℝ)) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul htaupos.le]
            norm_num
          _ = tau ^ ((1 / 4 : ℝ) * 2) := by ring_nf
          _ = (tau ^ (1 / 4 : ℝ)) ^ 2 := by
            rw [Real.rpow_mul htaupos.le]
            exact Real.rpow_natCast _ 2
  have hden : 0 < tau * (tau ^ (1 / 4 : ℝ)) ^ 2 := by positivity
  calc
    ‖deriv (fun u : ℝ =>
        RHTower.smoothAFEZetaSquareDualWeight u ((m : ℝ) * N)) tau‖
        ≤ C * (((m : ℝ) * N) ^ (1 / 4 : ℝ)) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) :=
          hraw.trans (min_le_left _ _)
    _ ≤ C * (tau ^ (1 / 4 : ℝ)) ^ 2 /
          (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hquarter hC) hden.le
    _ = C / tau := by
      have hq : 0 < (tau ^ (1 / 4 : ℝ)) ^ 2 := by positivity
      field_simp [hq.ne', htaupos.ne']
    _ ≤ C / (N : ℝ) :=
      div_le_div_of_nonneg_left hC hNpos htau.1

private theorem derivative_le_high_conductor
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => RHTower.smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        min
          (C * Y ^ (1 / 4 : ℝ) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2))
          (C * (1 + tau) / Y))
    {N m : ℕ} {tau : ℝ} (hN : 4 ≤ N) (hm : 1 ≤ m)
    (htau : tau ∈ Set.Icc (N : ℝ) (2 * N)) :
    ‖deriv (fun u : ℝ =>
        RHTower.smoothAFEZetaSquareDualWeight u ((m : ℝ) * N)) tau‖ ≤
      3 * C / (m : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htau4 : 4 ≤ tau := (by exact_mod_cast hN : (4 : ℝ) ≤ N) |>.trans htau.1
  have hYpos : 0 < (m : ℝ) * N := mul_pos hmpos hNpos
  have hraw := hderiv htau4 hYpos
  have hratio : (1 + tau) / (N : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hNpos]
    nlinarith [htau.2]
  calc
    ‖deriv (fun u : ℝ =>
        RHTower.smoothAFEZetaSquareDualWeight u ((m : ℝ) * N)) tau‖
        ≤ C * (1 + tau) / ((m : ℝ) * N) :=
          hraw.trans (min_le_right _ _)
    _ = (C / (m : ℝ)) * ((1 + tau) / (N : ℝ)) := by
      field_simp [hmpos.ne', hNpos.ne']
    _ ≤ (C / (m : ℝ)) * 3 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 3 * C / (m : ℝ) := by ring

private def dualDerivativeMass (N : ℕ) (tau : ℝ) (k : ℕ) : ℝ :=
  (((k + 1).divisors.card : ℝ) ^ 2) *
    ‖deriv (fun u : ℝ =>
      RHTower.smoothAFEZetaSquareDualWeight u (((k + 1 : ℕ) : ℝ) * N)) tau‖ ^ 2

private theorem summable_dualDerivativeMass
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => RHTower.smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        min
          (C * Y ^ (1 / 4 : ℝ) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2))
          (C * (1 + tau) / Y))
    {N : ℕ} {tau : ℝ} (hN : 4 ≤ N)
    (htau : tau ∈ Set.Icc (N : ℝ) (2 * N)) :
    Summable (dualDerivativeMass N tau) := by
  have hbase : Summable (fun k : ℕ =>
      (((k + 1).divisors.card : ℝ) ^ 2) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    apply (summable_divisorSquare_div_sq.comp_injective Nat.succ_injective).congr
    intro k
    norm_cast
  have hmajor : Summable (fun k : ℕ =>
      (9 * C ^ 2) *
        ((((k + 1).divisors.card : ℝ) ^ 2) / ((k + 1 : ℕ) : ℝ) ^ 2)) :=
    hbase.mul_left (9 * C ^ 2)
  refine Summable.of_nonneg_of_le
    (fun k => by unfold dualDerivativeMass; positivity) (fun k => ?_) hmajor
  have hpoint := derivative_le_high_conductor hC hderiv hN
    (show 1 ≤ k + 1 by omega) htau
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hpoint 2
  unfold dualDerivativeMass
  calc
    (((k + 1).divisors.card : ℝ) ^ 2) *
          ‖deriv (fun u : ℝ =>
            RHTower.smoothAFEZetaSquareDualWeight u (((k + 1 : ℕ) : ℝ) * N)) tau‖ ^ 2
        ≤ (((k + 1).divisors.card : ℝ) ^ 2) *
            (3 * C / ((k + 1 : ℕ) : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = (9 * C ^ 2) *
        ((((k + 1).divisors.card : ℝ) ^ 2) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
      ring

private theorem sum_range_divisorSquare_succ_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ range N, (((k + 1).divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3 := by
  have hmoment := sum_card_divisors_pow_le_polylog 2 N hN
  have heq :
      ∑ k ∈ range N, (((k + 1).divisors.card : ℝ) ^ 2) =
        ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2) := by
    rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by ext m; simp]
    rw [Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  rw [heq]
  simpa using hmoment

private theorem finite_low_dualDerivativeMass_le
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => RHTower.smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        min
          (C * Y ^ (1 / 4 : ℝ) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2))
          (C * (1 + tau) / Y))
    {N : ℕ} {tau : ℝ} (hN : 4 ≤ N)
    (htau : tau ∈ Set.Icc (N : ℝ) (2 * N)) :
    ∑ k ∈ range N, dualDerivativeMass N tau k ≤
      C ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint : ∀ k ∈ range N,
      dualDerivativeMass N tau k ≤
        (((k + 1).divisors.card : ℝ) ^ 2) * (C / (N : ℝ)) ^ 2 := by
    intro k hk
    have hkN : k + 1 ≤ N := by simpa using mem_range.mp hk
    have hcarrier := derivative_le_low_conductor hC hderiv hN
      (show 1 ≤ k + 1 by omega) hkN htau
    unfold dualDerivativeMass
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hcarrier 2) (by positivity)
  calc
    ∑ k ∈ range N, dualDerivativeMass N tau k
        ≤ ∑ k ∈ range N,
            (((k + 1).divisors.card : ℝ) ^ 2) * (C / (N : ℝ)) ^ 2 :=
          sum_le_sum hpoint
    _ = (C / (N : ℝ)) ^ 2 *
          ∑ k ∈ range N, (((k + 1).divisors.card : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro k hk
      ring
    _ ≤ (C / (N : ℝ)) ^ 2 *
          ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (sum_range_divisorSquare_succ_le N (by omega)) (sq_nonneg _)
    _ = C ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by
      field_simp [hNpos.ne']

private theorem tsum_high_dualDerivativeMass_le
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => RHTower.smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        min
          (C * Y ^ (1 / 4 : ℝ) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2))
          (C * (1 + tau) / Y))
    {N : ℕ} {tau : ℝ} (hN : 4 ≤ N)
    (htau : tau ∈ Set.Icc (N : ℝ) (2 * N)) :
    ∑' k : ℕ, dualDerivativeMass N tau (k + N) ≤
      288 * C ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by
  let tail : ℕ → ℝ := fun k =>
    (((N + 1 + k).divisors.card : ℝ) ^ 2) /
      ((N + 1 + k : ℕ) : ℝ) ^ 2
  have htail : Summable tail := by
    have hinj : Function.Injective (fun k : ℕ => N + 1 + k) := by
      intro a b hab
      exact Nat.add_left_cancel hab
    apply (summable_divisorSquare_div_sq.comp_injective hinj).congr
    intro k
    unfold tail
    norm_cast
  have hmass := summable_dualDerivativeMass hC hderiv hN htau
  have hmassShift : Summable (fun k : ℕ => dualDerivativeMass N tau (k + N)) := by
    exact hmass.comp_injective (fun a b hab => Nat.add_right_cancel hab)
  have hpoint : ∀ k : ℕ,
      dualDerivativeMass N tau (k + N) ≤ (9 * C ^ 2) * tail k := by
    intro k
    have hm : 1 ≤ (k + N) + 1 := by omega
    have hcarrier := derivative_le_high_conductor hC hderiv hN hm htau
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hcarrier 2
    unfold dualDerivativeMass tail
    calc
      ((((k + N) + 1).divisors.card : ℝ) ^ 2) *
            ‖deriv (fun u : ℝ =>
              RHTower.smoothAFEZetaSquareDualWeight u
                (((((k + N) + 1 : ℕ) : ℝ)) * N)) tau‖ ^ 2
          ≤ ((((k + N) + 1).divisors.card : ℝ) ^ 2) *
              (3 * C / ((((k + N) + 1 : ℕ) : ℝ))) ^ 2 :=
            mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = (9 * C ^ 2) *
          ((((N + 1 + k).divisors.card : ℝ) ^ 2) /
            ((N + 1 + k : ℕ) : ℝ) ^ 2) := by
        rw [show (k + N) + 1 = N + 1 + k by omega]
        ring
  have hcompare := hmassShift.tsum_le_tsum hpoint (htail.mul_left (9 * C ^ 2))
  rw [htail.tsum_mul_left] at hcompare
  have htailBound := tsum_shift_divisorSquare_div_sq_le N (by omega)
  calc
    ∑' k : ℕ, dualDerivativeMass N tau (k + N)
        ≤ (9 * C ^ 2) * ∑' k : ℕ, tail k := hcompare
    _ ≤ (9 * C ^ 2) *
          (32 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left htailBound (by positivity)
    _ = 288 * C ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by ring

private theorem tsum_dualDerivativeMass_le
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => RHTower.smoothAFEZetaSquareDualWeight u Y) tau‖ ≤
        min
          (C * Y ^ (1 / 4 : ℝ) /
            (tau * (tau ^ (1 / 4 : ℝ)) ^ 2))
          (C * (1 + tau) / Y))
    {N : ℕ} {tau : ℝ} (hN : 4 ≤ N)
    (htau : tau ∈ Set.Icc (N : ℝ) (2 * N)) :
    ∑' k : ℕ, dualDerivativeMass N tau k ≤
      289 * C ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by
  have hmass := summable_dualDerivativeMass hC hderiv hN htau
  have hlow := finite_low_dualDerivativeMass_le hC hderiv hN htau
  have hhigh := tsum_high_dualDerivativeMass_le hC hderiv hN htau
  rw [← hmass.sum_add_tsum_nat_add N]
  calc
    (∑ k ∈ range N, dualDerivativeMass N tau k) +
          ∑' k : ℕ, dualDerivativeMass N tau (k + N)
        ≤ C ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) +
          288 * C ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) :=
            add_le_add hlow hhigh
    _ = 289 * C ^ 2 * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by ring

/-- **Dyadic square-carrier derivative mass law.**  On `τ ∈ [N,2N]`, with AFE smoothing scale
`x=N`, the complete divisor-weighted derivative mass is `O(log³ N / N)`.  This is the precise
coefficient estimate needed to combine affine mean square with Duhamel transport. -/
theorem exists_tsum_divisorSquare_norm_deriv_dualWeight_sq_le_dyadic :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N : ℕ} {tau : ℝ},
      4 ≤ N → tau ∈ Set.Icc (N : ℝ) (2 * N) →
      (∑' k : ℕ,
        (((k + 1).divisors.card : ℝ) ^ 2) *
          ‖deriv (fun u : ℝ =>
            RHTower.smoothAFEZetaSquareDualWeight u
              (((k + 1 : ℕ) : ℝ) * N)) tau‖ ^ 2) ≤
        K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by
  obtain ⟨C, hC, hderiv⟩ :=
    RHTower.exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_two_sided
  refine ⟨289 * C ^ 2, by positivity, ?_⟩
  intro N tau hN htau
  simpa [dualDerivativeMass] using
    tsum_dualDerivativeMass_le hC hderiv hN htau

/-- The dyadic divisor-weighted derivative mass is summable at every admissible block height. -/
theorem summable_divisorSquare_norm_deriv_dualWeight_sq_dyadic
    {N : ℕ} {tau : ℝ} (hN : 4 ≤ N)
    (htau : tau ∈ Set.Icc (N : ℝ) (2 * N)) :
    Summable (fun k : ℕ =>
      (((k + 1).divisors.card : ℝ) ^ 2) *
        ‖deriv (fun u : ℝ =>
          RHTower.smoothAFEZetaSquareDualWeight u
            (((k + 1 : ℕ) : ℝ) * N)) tau‖ ^ 2) := by
  obtain ⟨C, hC, hderiv⟩ :=
    RHTower.exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_two_sided
  apply (summable_dualDerivativeMass hC hderiv hN htau).congr
  intro k
  unfold dualDerivativeMass
  norm_cast

end RHTower.Sieve
