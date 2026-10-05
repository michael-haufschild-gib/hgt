import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated
import GaloisForLFunctions.RHTower.ZetaMultipleLandauZeroFree
import GaloisForLFunctions.RHTower.HighBlockDualWeightVariation
import GaloisForLFunctions.RHTower.ChebyshevLagZeroWindowTerm
import GaloisForLFunctions.RHTower.BaezDuarteDualSequence

/-!
# The Báez--Duarte distances decay at most like `1/√(log N)`

Unconditionally, `d_N² ≥ c/log N` for every `N ≥ 2` (`exists_div_log_le_bdDistDiscrete_sq`):
the distances `d_N → 0` that are equivalent to RH cannot go to zero faster than `1/√(log N)`.

**The dual vector.**  Fix a zero `ρ = ½ + iγ` of `ζ` and `Y = N⁷`, and let
`a_k = k^{−ρ}(Y − k + 1)/Y` for `k ≤ Y` (`zeroDual`).  Writing `a_k = (1/Y) Σ_{k ≤ j ≤ Y} k^{−ρ}`,

`Σ_{m ∣ k} a_k − (1/m) Σ_k a_k = (1/Y) Σ_{j ≤ Y} (m^{−ρ} S_ρ(⌊j/m⌋) − S_ρ(j)/m)`,

where `S_ρ(M) = Σ_{k ≤ M} k^{−ρ} = M^{1−ρ}/(1−ρ) + O(|ρ| M^{−1/2})` because `ζ(ρ) = 0`.  The main
terms cancel exactly (`m^{−ρ}(j/m)^{1−ρ} = j^{1−ρ}/m`), so every defect is `≤ (12|ρ| + 4)/√Y`
(`norm_bdModDefect_zeroDual_le`), while the energy `Σ k(k+1)|a_k − a_{k+1}|²` is
`≤ 2|ρ|²(1 + log Y) + 2` (`bdDualEnergyC_zeroDual_le`).

**Exactness.**  The Möbius correction of `BaezDuarteDualSequence` cancels the defects exactly at a
cost `O(N⁷/Y)` in energy, and the real part of the corrected sequence is a dual sequence with value
`1` at `k = 1`.  Hence `1 ≤ d_N² (4|ρ|²(1 + 7 log N) + O(1))`.
-/

open Finset Complex

namespace RHTower

noncomputable section

/-! ## Partial sums at a zero on the critical line -/

/-- `S_ρ(M) = Σ_{k ≤ M} k^{−ρ}`. -/
def zeroPartialSum (ρ : ℂ) (M : ℕ) : ℂ := ∑ k ∈ Icc 1 M, (k : ℂ) ^ (-ρ)

theorem norm_zeroPartialSum_sub_le {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : ρ.re = 1 / 2)
    {M : ℕ} (hM : 1 ≤ M) :
    ‖zeroPartialSum ρ M - (M : ℂ) ^ (1 - ρ) / (1 - ρ)‖ ≤ 2 * ‖ρ‖ * ((M : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hρ0 : 0 < ρ.re := by rw [hre]; norm_num
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
  have h := Sieve.riemannZeta_eq_sum_add_tail hρ0 hρ1 hM
  have hI := Sieve.norm_integral_Ioi_fract_cpow_le hρ0 hM
  set I := ∫ t in Set.Ioi (M : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1)) with hIdef
  have hS : zeroPartialSum ρ M = ∑ k ∈ Icc 1 M, ((k : ℝ) : ℂ) ^ (-ρ) := by
    unfold zeroPartialSum; simp
  have hsub : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hsub' : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have heq : zeroPartialSum ρ M - (M : ℂ) ^ (1 - ρ) / (1 - ρ) = ρ * I := by
    rw [hS]
    rw [hρ] at h
    have hcast : ((M : ℝ) : ℂ) = (M : ℂ) := by simp
    rw [hcast] at h
    have : (M : ℂ) ^ (1 - ρ) / (ρ - 1) = -((M : ℂ) ^ (1 - ρ) / (1 - ρ)) := by
      rw [show ρ - 1 = -(1 - ρ) by ring, div_neg]
    rw [this] at h
    linear_combination -h
  rw [heq, norm_mul]
  rw [hre] at hI
  calc ‖ρ‖ * ‖I‖ ≤ ‖ρ‖ * ((M : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2)) :=
        mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ = 2 * ‖ρ‖ * ((M : ℝ) ^ (-(1 / 2 : ℝ))) := by ring

theorem rpow_neg_one_half_eq_inv_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx, Real.sqrt_eq_rpow]

theorem norm_natCast_cpow_neg_of_re {ρ : ℂ} (hre : ρ.re = 1 / 2) {k : ℕ} (hk : 1 ≤ k) :
    ‖(k : ℂ) ^ (-ρ)‖ = (Real.sqrt k)⁻¹ := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re, hre,
    rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg k)]

theorem inv_sqrt_le_two_mul_sqrt_sub (k : ℕ) :
    (Real.sqrt ((k : ℝ) + 1))⁻¹ ≤ 2 * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k) := by
  have ha := Real.sqrt_nonneg (k : ℝ)
  have hb : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
  have hsq' : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hab : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  rw [inv_le_iff_one_le_mul₀ hb]
  nlinarith [sq_nonneg (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k)]

/-- `Σ_{k ≤ Y} k^{−1/2} ≤ 2√Y`. -/
theorem sum_Icc_inv_sqrt_le (Y : ℕ) : ∑ k ∈ Icc 1 Y, (Real.sqrt k)⁻¹ ≤ 2 * Real.sqrt Y := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [sum_Icc_succ_top (by omega), Nat.cast_succ]
    have := inv_sqrt_le_two_mul_sqrt_sub Y
    linarith

theorem norm_zeroPartialSum_le {ρ : ℂ} (hre : ρ.re = 1 / 2) (M : ℕ) :
    ‖zeroPartialSum ρ M‖ ≤ 2 * Real.sqrt M := by
  unfold zeroPartialSum
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Icc 1 M, ‖(k : ℂ) ^ (-ρ)‖ = ∑ k ∈ Icc 1 M, (Real.sqrt k)⁻¹ :=
        sum_congr rfl fun k hk => norm_natCast_cpow_neg_of_re hre (mem_Icc.mp hk).1
    _ ≤ 2 * Real.sqrt M := sum_Icc_inv_sqrt_le M

/-! ## Multiples -/

/-- `Σ_{k ≤ j, n ∣ k} k^{−ρ} = n^{−ρ} S_ρ(⌊j/n⌋)`. -/
theorem sum_filter_dvd_cpow_eq {n : ℕ} (hn : 1 ≤ n) (ρ : ℂ) (j : ℕ) :
    ∑ k ∈ (Icc 1 j).filter (fun k => n ∣ k), (k : ℂ) ^ (-ρ) =
      (n : ℂ) ^ (-ρ) * zeroPartialSum ρ (j / n) := by
  unfold zeroPartialSum
  rw [mul_sum]
  refine sum_nbij' (fun k => k / n) (fun i => n * i) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hkj⟩, ⟨i, rfl⟩⟩ := hk
    rw [Nat.mul_div_cancel_left i (by omega)]
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos i with h | h
      · subst h; omega
      · exact h
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [Nat.mul_comm n i])
  · intro i hi
    simp only [mem_filter, mem_Icc] at hi ⊢
    refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right n i⟩
    have := (Nat.le_div_iff_mul_le (by omega)).mp hi.2
    linarith [Nat.mul_comm n i]
  · intro k hk
    simp only [mem_filter] at hk
    obtain ⟨_, ⟨i, rfl⟩⟩ := hk
    rw [Nat.mul_div_cancel_left i (by omega)]
  · intro i _
    exact Nat.mul_div_cancel_left i (by omega)
  · intro k hk
    simp only [mem_filter] at hk
    obtain ⟨_, ⟨i, rfl⟩⟩ := hk
    rw [Nat.mul_div_cancel_left i (by omega)]
    push_cast
    exact Complex.natCast_mul_natCast_cpow n i (-ρ)

theorem natCast_cpow_neg_mul_cpow_one_sub {n M : ℕ} (hn : 1 ≤ n) (ρ : ℂ) :
    (n : ℂ) ^ (-ρ) * (M : ℂ) ^ (1 - ρ) = ((n * M : ℕ) : ℂ) ^ (1 - ρ) / n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h1 : (n : ℂ) ^ (1 - ρ) = (n : ℂ) * (n : ℂ) ^ (-ρ) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hn0, Complex.cpow_one]
  push_cast
  rw [Complex.natCast_mul_natCast_cpow, h1]
  field_simp

/-- **The multiple sums against the full sums.**  For `n, j ≥ 1`,
`|n^{−ρ} S_ρ(⌊j/n⌋) − S_ρ(j)/n| ≤ (6|ρ| + 2)/√j`. -/
theorem norm_cpow_mul_zeroPartialSum_div_sub_le {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : ρ.re = 1 / 2) {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    ‖(n : ℂ) ^ (-ρ) * zeroPartialSum ρ (j / n) - zeroPartialSum ρ j / n‖ ≤
      (6 * ‖ρ‖ + 2) * (Real.sqrt j)⁻¹ := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
  have hsub : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hnorm_n : ‖(n : ℂ) ^ (-ρ)‖ = (Real.sqrt n)⁻¹ := norm_natCast_cpow_neg_of_re hre hn
  have hρ0 : 0 ≤ ‖ρ‖ := norm_nonneg _
  rcases Nat.lt_or_ge j n with hjn | hjn
  · -- no multiple of `n` below `j`
    have hdiv : j / n = 0 := Nat.div_eq_of_lt hjn
    have hS0 : zeroPartialSum ρ 0 = 0 := by simp [zeroPartialSum]
    rw [hdiv, hS0, mul_zero, zero_sub, norm_neg, norm_div, Complex.norm_natCast]
    have h1 := norm_zeroPartialSum_le hre j
    have hsjj : Real.sqrt j * Real.sqrt j = j := Real.mul_self_sqrt hj0.le
    have hjn' : (j : ℝ) < n := by exact_mod_cast hjn
    rw [div_le_iff₀ hn0]
    calc ‖zeroPartialSum ρ j‖ ≤ 2 * Real.sqrt j := h1
      _ = 2 * (Real.sqrt j)⁻¹ * j := by
          field_simp
          rw [Real.sq_sqrt hj0.le]
      _ ≤ (6 * ‖ρ‖ + 2) * (Real.sqrt j)⁻¹ * n := by
          have : 2 * (Real.sqrt j)⁻¹ ≤ (6 * ‖ρ‖ + 2) * (Real.sqrt j)⁻¹ :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          nlinarith [inv_pos.mpr hsj]
  · set M := j / n with hM
    have hM1 : 1 ≤ M := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have hdecomp := Nat.div_add_mod j n
    rw [← hM] at hdecomp
    have hmod := Nat.mod_lt j (by omega : n > 0)
    have hnM_le : n * M ≤ j := Nat.mul_div_le j n
    have hnM1 : 1 ≤ n * M := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hnM0 : (0 : ℝ) < ((n * M : ℕ) : ℝ) := by exact_mod_cast hnM1
    have hj2 : (j : ℝ) ≤ 2 * ((n * M : ℕ) : ℝ) := by
      have : j ≤ 2 * (n * M) := by nlinarith
      exact_mod_cast this
    -- the three pieces
    set eM := zeroPartialSum ρ M - (M : ℂ) ^ (1 - ρ) / (1 - ρ) with heM
    set ej := zeroPartialSum ρ j - (j : ℂ) ^ (1 - ρ) / (1 - ρ) with hej
    have hid : (n : ℂ) ^ (-ρ) * zeroPartialSum ρ M - zeroPartialSum ρ j / n =
        (n : ℂ) ^ (-ρ) * eM - ej / n +
          ((((n * M : ℕ) : ℂ) ^ (1 - ρ) - (j : ℂ) ^ (1 - ρ)) / n / (1 - ρ)) := by
      have h := natCast_cpow_neg_mul_cpow_one_sub hn (M := M) ρ
      have key : (n : ℂ) ^ (-ρ) * ((M : ℂ) ^ (1 - ρ) / (1 - ρ)) =
          ((n * M : ℕ) : ℂ) ^ (1 - ρ) / n / (1 - ρ) := by
        rw [← mul_div_assoc, h]
      have hSM : zeroPartialSum ρ M = eM + (M : ℂ) ^ (1 - ρ) / (1 - ρ) := by rw [heM]; ring
      have hSj : zeroPartialSum ρ j = ej + (j : ℂ) ^ (1 - ρ) / (1 - ρ) := by rw [hej]; ring
      rw [hSM, hSj, mul_add, key]
      ring
    rw [hid]
    have hbM := norm_zeroPartialSum_sub_le hρ hre hM1
    have hbj := norm_zeroPartialSum_sub_le hρ hre hj
    rw [rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg _)] at hbM hbj
    -- the power difference
    have hpow : ‖((n * M : ℕ) : ℂ) ^ (1 - ρ) - (j : ℂ) ^ (1 - ρ)‖ ≤
        ‖1 - ρ‖ * n * (Real.sqrt ((n * M : ℕ) : ℝ))⁻¹ := by
      have hre1 : (1 - ρ).re = 1 / 2 := by simp [hre]; norm_num
      have h := norm_ofReal_cpow_sub_cpow_le hnM0 (t := (j : ℝ))
        (by exact_mod_cast hnM_le) (ρ := 1 - ρ) (by rw [hre1]; norm_num) (by rw [hre1]; norm_num)
      rw [hre1, show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num,
        rpow_neg_one_half_eq_inv_sqrt _ hnM0.le] at h
      rw [norm_sub_rev]
      push_cast at h ⊢
      refine h.trans ?_
      have hgap : (j : ℝ) - ((n : ℝ) * (M : ℝ)) ≤ n := by
        have : j < n * M + n := by omega
        have : (j : ℝ) < (n : ℝ) * (M : ℝ) + n := by exact_mod_cast this
        linarith
      have hgap0 : 0 ≤ (j : ℝ) - ((n : ℝ) * (M : ℝ)) := by
        have : ((n * M : ℕ) : ℝ) ≤ j := by exact_mod_cast hnM_le
        push_cast at this; linarith
      have hinv0 : 0 ≤ (Real.sqrt ((n : ℝ) * (M : ℝ)))⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (norm_nonneg _)) hinv0
    have hsqnM : (Real.sqrt ((n * M : ℕ) : ℝ))⁻¹ ≤ 2 * (Real.sqrt j)⁻¹ := by
      have hsnM : 0 < Real.sqrt ((n * M : ℕ) : ℝ) := Real.sqrt_pos.mpr hnM0
      rw [inv_le_iff_one_le_mul₀ hsnM]
      have h2 : Real.sqrt j ≤ Real.sqrt 2 * Real.sqrt ((n * M : ℕ) : ℝ) := by
        rw [← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt hj2
      have hs2 : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have : Real.sqrt j ≤ 2 * Real.sqrt ((n * M : ℕ) : ℝ) := by nlinarith [Real.sqrt_nonneg 2]
      rw [show 2 * (Real.sqrt j)⁻¹ * Real.sqrt ((n * M : ℕ) : ℝ) =
        (2 * Real.sqrt ((n * M : ℕ) : ℝ)) / Real.sqrt j by field_simp]
      rw [le_div_iff₀ hsj]; linarith
    have hsqnM' : (Real.sqrt n)⁻¹ * (Real.sqrt M)⁻¹ = (Real.sqrt ((n * M : ℕ) : ℝ))⁻¹ := by
      push_cast; rw [Real.sqrt_mul (Nat.cast_nonneg n), mul_inv]
    have t1 : ‖(n : ℂ) ^ (-ρ) * eM‖ ≤ 4 * ‖ρ‖ * (Real.sqrt j)⁻¹ := by
      rw [norm_mul, hnorm_n]
      calc (Real.sqrt n)⁻¹ * ‖eM‖ ≤ (Real.sqrt n)⁻¹ * (2 * ‖ρ‖ * (Real.sqrt M)⁻¹) :=
            mul_le_mul_of_nonneg_left hbM (by positivity)
        _ = 2 * ‖ρ‖ * (Real.sqrt ((n * M : ℕ) : ℝ))⁻¹ := by rw [← hsqnM']; ring
        _ ≤ 2 * ‖ρ‖ * (2 * (Real.sqrt j)⁻¹) := mul_le_mul_of_nonneg_left hsqnM (by positivity)
        _ = 4 * ‖ρ‖ * (Real.sqrt j)⁻¹ := by ring
    have t2 : ‖ej / n‖ ≤ 2 * ‖ρ‖ * (Real.sqrt j)⁻¹ := by
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ hn0]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc ‖ej‖ ≤ 2 * ‖ρ‖ * (Real.sqrt j)⁻¹ := hbj
        _ ≤ 2 * ‖ρ‖ * (Real.sqrt j)⁻¹ * n := le_mul_of_one_le_right (by positivity) hn1
    have t3 : ‖(((n * M : ℕ) : ℂ) ^ (1 - ρ) - (j : ℂ) ^ (1 - ρ)) / n / (1 - ρ)‖ ≤
        2 * (Real.sqrt j)⁻¹ := by
      have h1ρ : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hsub
      rw [norm_div, norm_div, Complex.norm_natCast, div_div, div_le_iff₀ (by positivity)]
      calc _ ≤ ‖1 - ρ‖ * n * (Real.sqrt ((n * M : ℕ) : ℝ))⁻¹ := hpow
        _ ≤ ‖1 - ρ‖ * n * (2 * (Real.sqrt j)⁻¹) :=
            mul_le_mul_of_nonneg_left hsqnM (by positivity)
        _ = 2 * (Real.sqrt j)⁻¹ * (n * ‖1 - ρ‖) := by ring
    have e1 := norm_add_le ((n : ℂ) ^ (-ρ) * eM - ej / n)
      ((((n * M : ℕ) : ℂ) ^ (1 - ρ) - (j : ℂ) ^ (1 - ρ)) / n / (1 - ρ))
    have e2 := norm_sub_le ((n : ℂ) ^ (-ρ) * eM) (ej / n)
    nlinarith [t1, t2, t3, e1, e2]

/-! ## The dual sequence of a critical zero -/

/-- `a_k = k^{−ρ}(Y − k + 1)/Y` for `1 ≤ k ≤ Y`, and `0` otherwise. -/
def zeroDual (ρ : ℂ) (Y : ℕ) (k : ℕ) : ℂ :=
  if k ∈ Icc 1 Y then (k : ℂ) ^ (-ρ) * ((((Y : ℝ) - k + 1) / Y : ℝ) : ℂ) else 0

theorem zeroDual_eq_zero {ρ : ℂ} {Y k : ℕ} (hk : Y < k) : zeroDual ρ Y k = 0 := by
  unfold zeroDual
  rw [if_neg (by simp only [mem_Icc]; omega)]

theorem zeroDual_one {ρ : ℂ} {Y : ℕ} (hY : 1 ≤ Y) : zeroDual ρ Y 1 = 1 := by
  unfold zeroDual
  rw [if_pos (by simp only [mem_Icc]; omega)]
  have hY0 : (Y : ℝ) ≠ 0 := by exact_mod_cast (by omega : Y ≠ 0)
  simp only [Nat.cast_one, Complex.one_cpow, one_mul]
  rw [show ((Y : ℝ) - 1 + 1) / Y = 1 by field_simp; ring]
  simp

theorem zeroDual_eq_sum {ρ : ℂ} {Y k : ℕ} (hk : k ∈ Icc 1 Y) :
    zeroDual ρ Y k = (1 / (Y : ℂ)) * ∑ _j ∈ Icc k Y, (k : ℂ) ^ (-ρ) := by
  unfold zeroDual
  rw [if_pos hk, sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hk' := mem_Icc.mp hk
  have hcast : ((Y + 1 - k : ℕ) : ℂ) = (Y : ℂ) - k + 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast]
  push_cast
  ring

/-- `Σ_{k ≤ K, n ∣ k} a_k = (1/Y) Σ_{j ≤ Y} n^{−ρ} S_ρ(⌊j/n⌋)` for `K ≥ Y`. -/
theorem sum_filter_dvd_zeroDual {ρ : ℂ} {Y K n : ℕ} (hYK : Y ≤ K) (hn : 1 ≤ n) :
    ∑ k ∈ (Icc 1 K).filter (fun k => n ∣ k), zeroDual ρ Y k =
      (1 / (Y : ℂ)) * ∑ j ∈ Icc 1 Y, (n : ℂ) ^ (-ρ) * zeroPartialSum ρ (j / n) := by
  have hsub : (Icc 1 Y).filter (fun k => n ∣ k) ⊆ (Icc 1 K).filter (fun k => n ∣ k) := by
    intro k hk; simp only [mem_filter, mem_Icc] at hk ⊢; omega
  rw [← sum_subset hsub (fun k hk hk' => by
    simp only [mem_filter, mem_Icc] at hk hk'
    exact zeroDual_eq_zero (by omega))]
  rw [sum_congr rfl fun k hk => zeroDual_eq_sum (mem_filter.mp hk).1, ← mul_sum]
  congr 1
  rw [sum_comm' (t' := Icc 1 Y) (s' := fun j => (Icc 1 j).filter (fun k => n ∣ k))]
  · exact sum_congr rfl fun j _ => sum_filter_dvd_cpow_eq hn ρ j
  · intro k j
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩; exact ⟨⟨⟨h1, h4⟩, h3⟩, by omega, h5⟩
    · rintro ⟨⟨⟨h1, h4⟩, h3⟩, h6, h5⟩; exact ⟨⟨⟨h1, by omega⟩, h3⟩, h4, h5⟩

/-- **The defect of the zero dual.**  For `1 ≤ m ≤ Y ≤ K`,
`|Σ_{m ∣ k} a_k − (1/m) Σ a_k| ≤ (12|ρ| + 4)/√Y`. -/
theorem norm_bdModDefect_zeroDual_le {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : ρ.re = 1 / 2)
    {Y K m : ℕ} (hY : 1 ≤ Y) (hYK : Y ≤ K) (hm : 1 ≤ m) :
    ‖bdModDefect (zeroDual ρ Y) K m‖ ≤ (12 * ‖ρ‖ + 4) * (Real.sqrt Y)⁻¹ := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hall := sum_filter_dvd_zeroDual (ρ := ρ) hYK (le_refl 1)
  have hall' : ∑ k ∈ Icc 1 K, zeroDual ρ Y k =
      (1 / (Y : ℂ)) * ∑ j ∈ Icc 1 Y, zeroPartialSum ρ j := by
    rw [← filter_true_of_mem (s := Icc 1 K) (p := fun k => 1 ∣ k) (fun k _ => one_dvd k), hall]
    simp
  have hdef : bdModDefect (zeroDual ρ Y) K m = (1 / (Y : ℂ)) *
      ∑ j ∈ Icc 1 Y, ((m : ℂ) ^ (-ρ) * zeroPartialSum ρ (j / m) - zeroPartialSum ρ j / m) := by
    unfold bdModDefect
    rw [sum_filter_dvd_zeroDual hYK hm, hall', sum_sub_distrib, ← sum_div]
    ring
  rw [hdef, norm_mul]
  have hnY : ‖(1 / (Y : ℂ))‖ = 1 / Y := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hnY]
  have hsum : ‖∑ j ∈ Icc 1 Y, ((m : ℂ) ^ (-ρ) * zeroPartialSum ρ (j / m) -
      zeroPartialSum ρ j / m)‖ ≤ (6 * ‖ρ‖ + 2) * (2 * Real.sqrt Y) := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum fun j hj => norm_cpow_mul_zeroPartialSum_div_sub_le hρ hre hm
      (mem_Icc.mp hj).1).trans ?_
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_Icc_inv_sqrt_le Y) (by positivity)
  calc 1 / (Y : ℝ) * ‖_‖ ≤ 1 / (Y : ℝ) * ((6 * ‖ρ‖ + 2) * (2 * Real.sqrt Y)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (12 * ‖ρ‖ + 4) * (Real.sqrt Y)⁻¹ := by
        have hinv : 1 / (Y : ℝ) = (Real.sqrt Y)⁻¹ * (Real.sqrt Y)⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hY0.le, one_div]
        rw [hinv]; field_simp; ring

/-! ## The energy of the zero dual -/

theorem mul_sq_inv_sqrt_sub_le (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * ((k : ℝ) + 1) * ((Real.sqrt k)⁻¹ - (Real.sqrt ((k : ℝ) + 1))⁻¹) ^ 2 ≤
      1 / (4 * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set a := Real.sqrt (k : ℝ) with ha
  set b := Real.sqrt ((k : ℝ) + 1) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr hk0
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have ha2 : a ^ 2 = k := Real.sq_sqrt hk0.le
  have hb2 : b ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have e1 : (k : ℝ) * ((k : ℝ) + 1) * (a⁻¹ - b⁻¹) ^ 2 = (b - a) ^ 2 := by
    rw [← hb2, ← ha2]; field_simp
  rw [e1]
  have hsum : (b - a) * (b + a) = 1 := by nlinarith
  have hba : b - a ≤ 1 / (2 * a) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hba0 : 0 ≤ b - a := by linarith
  calc (b - a) ^ 2 ≤ (1 / (2 * a)) ^ 2 := pow_le_pow_left₀ hba0 hba 2
    _ = 1 / (4 * k) := by rw [← ha2]; field_simp; ring

/-- **The energy of the zero dual.**  `Σ k(k+1)|a_k − a_{k+1}|² ≤ 2|ρ|²(1 + log Y) + 2`. -/
theorem bdDualEnergyC_zeroDual_le {ρ : ℂ} (hre : ρ.re = 1 / 2) {Y : ℕ} (hY : 1 ≤ Y) (K : ℕ) :
    bdDualEnergyC (zeroDual ρ Y) K ≤ 2 * ‖ρ‖ ^ 2 * (1 + Real.log Y) + 2 := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hρre : ρ.re ≠ 0 := by rw [hre]; norm_num
  -- the formula on `[1, Y + 1]`
  have hform : ∀ k, 1 ≤ k → k ≤ Y + 1 →
      zeroDual ρ Y k = (k : ℂ) ^ (-ρ) * ((((Y : ℝ) - k + 1) / Y : ℝ) : ℂ) := by
    intro k hk1 hk2
    unfold zeroDual
    split_ifs with h
    · rfl
    · have : k = Y + 1 := by simp only [mem_Icc] at h; omega
      subst this
      push_cast
      simp
  -- each term
  have hterm : ∀ n ∈ range K, ((n : ℝ) + 1) * ((n : ℝ) + 2) *
      ‖zeroDual ρ Y (n + 1) - zeroDual ρ Y (n + 2)‖ ^ 2 ≤
      if n < Y then 2 * ‖ρ‖ ^ 2 / ((n : ℝ) + 1) + 2 / Y else 0 := by
    intro n _
    split_ifs with hn
    · set k := n + 1 with hk
      have hk1 : 1 ≤ k := by omega
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      rw [hform (n + 1) (by omega) (by omega), hform (n + 2) (by omega) (by omega)]
      have hcastk : ((n : ℝ) + 1) = (k : ℝ) := by rw [hk]; push_cast; ring
      have hcastk2 : ((n : ℝ) + 2) = (k : ℝ) + 1 := by rw [hk]; push_cast; ring
      rw [hcastk, hcastk2]
      have hn2 : ((n + 2 : ℕ) : ℂ) = ((k : ℝ) + 1 : ℝ) := by rw [hk]; push_cast; ring
      have hn1 : ((n + 1 : ℕ) : ℂ) = ((k : ℝ) : ℝ) := by rw [hk]; push_cast; ring
      have hw1 : ((((Y : ℝ) - ((n + 1 : ℕ) : ℝ) + 1) / Y : ℝ) : ℂ) =
          ((((Y : ℝ) - k + 1) / Y : ℝ) : ℂ) := by rw [hk]
      have hw2 : ((((Y : ℝ) - ((n + 2 : ℕ) : ℝ) + 1) / Y : ℝ) : ℂ) =
          ((((Y : ℝ) - k + 1) / Y : ℝ) : ℂ) - ((1 / Y : ℝ) : ℂ) := by
        rw [hk]; push_cast; ring
      rw [hw1, hw2, hn1, hn2]
      set w : ℝ := ((Y : ℝ) - k + 1) / Y with hw
      have hw0 : 0 ≤ w := by
        rw [hw]; have : (k : ℝ) ≤ Y := by exact_mod_cast (by omega : k ≤ Y)
        exact div_nonneg (by linarith) hY0.le
      have hw1' : w ≤ 1 := by
        rw [hw, div_le_one hY0]; linarith
      have hdecomp : ((k : ℝ) : ℂ) ^ (-ρ) * (w : ℂ) -
          (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ) * ((w : ℂ) - ((1 / Y : ℝ) : ℂ)) =
          (((k : ℝ) : ℂ) ^ (-ρ) - (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ)) * (w : ℂ) +
            (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ) * ((1 / Y : ℝ) : ℂ) := by ring
      rw [hdecomp]
      have hdiff := norm_cpow_neg_sub_cpow_neg_le hρre hk0 (B := (k : ℝ) + 1) (by linarith)
      rw [hre, rpow_neg_one_half_eq_inv_sqrt _ hk0.le,
        rpow_neg_one_half_eq_inv_sqrt _ (by positivity), norm_sub_rev] at hdiff
      have hpow1 : ‖(((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ)‖ = (Real.sqrt ((k : ℝ) + 1))⁻¹ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, hre,
          rpow_neg_one_half_eq_inv_sqrt _ (by positivity)]
      set δ := (Real.sqrt k)⁻¹ - (Real.sqrt ((k : ℝ) + 1))⁻¹ with hδ
      have hδ0 : 0 ≤ δ := by
        rw [hδ, sub_nonneg]
        exact inv_anti₀ (Real.sqrt_pos.mpr hk0) (Real.sqrt_le_sqrt (by linarith))
      have hA : ‖(((k : ℝ) : ℂ) ^ (-ρ) - (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ)) * (w : ℂ)‖ ≤
          2 * ‖ρ‖ * δ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
        calc _ ≤ ‖ρ‖ * (δ / (1 / 2)) * 1 :=
              mul_le_mul hdiff hw1' hw0 (by positivity)
          _ = 2 * ‖ρ‖ * δ := by ring
      have hB : ‖(((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ) * ((1 / Y : ℝ) : ℂ)‖ ≤
          (Real.sqrt ((k : ℝ) + 1))⁻¹ / Y := by
        rw [norm_mul, hpow1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        ring_nf; rfl
      have hsum := norm_add_le
        ((((k : ℝ) : ℂ) ^ (-ρ) - (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ)) * (w : ℂ))
        ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ) * ((1 / Y : ℝ) : ℂ))
      set X := ‖(((k : ℝ) : ℂ) ^ (-ρ) - (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ)) * (w : ℂ) +
          (((k : ℝ) + 1 : ℝ) : ℂ) ^ (-ρ) * ((1 / Y : ℝ) : ℂ)‖ with hX
      have hX0 : 0 ≤ X := norm_nonneg _
      have hXle : X ≤ 2 * ‖ρ‖ * δ + (Real.sqrt ((k : ℝ) + 1))⁻¹ / Y := by linarith
      have hsq : X ^ 2 ≤ 2 * (2 * ‖ρ‖ * δ) ^ 2 + 2 * ((Real.sqrt ((k : ℝ) + 1))⁻¹ / Y) ^ 2 := by
        have := pow_le_pow_left₀ hX0 hXle 2
        nlinarith [sq_nonneg (2 * ‖ρ‖ * δ - (Real.sqrt ((k : ℝ) + 1))⁻¹ / Y)]
      have hkk : (k : ℝ) * ((k : ℝ) + 1) * δ ^ 2 ≤ 1 / (4 * k) := mul_sq_inv_sqrt_sub_le k hk1
      have hkY : (k : ℝ) ≤ Y := by exact_mod_cast (by omega : k ≤ Y)
      have hsq1 : ((Real.sqrt ((k : ℝ) + 1))⁻¹) ^ 2 = 1 / ((k : ℝ) + 1) := by
        rw [inv_pow, Real.sq_sqrt (by positivity), one_div]
      have hwt : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) := by positivity
      calc (k : ℝ) * ((k : ℝ) + 1) * X ^ 2
          ≤ (k : ℝ) * ((k : ℝ) + 1) *
            (2 * (2 * ‖ρ‖ * δ) ^ 2 + 2 * ((Real.sqrt ((k : ℝ) + 1))⁻¹ / Y) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hwt
        _ = 8 * ‖ρ‖ ^ 2 * ((k : ℝ) * ((k : ℝ) + 1) * δ ^ 2) + 2 * (k : ℝ) / (Y : ℝ) ^ 2 := by
            rw [div_pow, hsq1]; field_simp; ring
        _ ≤ 8 * ‖ρ‖ ^ 2 * (1 / (4 * k)) + 2 * (Y : ℝ) / (Y : ℝ) ^ 2 := by
            gcongr
        _ = 2 * ‖ρ‖ ^ 2 / (k : ℝ) + 2 / Y := by field_simp; ring
    · rw [zeroDual_eq_zero (by omega), zeroDual_eq_zero (by omega), sub_zero, norm_zero]
      simp
  unfold bdDualEnergyC
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter]
  have hsub : (range K).filter (fun n => n < Y) ⊆ range Y := fun n hn => by
    simp only [mem_filter, mem_range] at hn ⊢; exact hn.2
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hharm : ∑ n ∈ range Y, 2 * ‖ρ‖ ^ 2 / ((n : ℝ) + 1) =
      2 * ‖ρ‖ ^ 2 * (harmonic Y : ℝ) := by
    rw [harmonic, Rat.cast_sum, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    push_cast
    ring
  rw [hharm]
  have hH := harmonic_le_one_add_log Y
  have h2 : (Y : ℝ) * (2 / Y) = 2 := by field_simp
  rw [h2]
  have hρ2 : 0 ≤ 2 * ‖ρ‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hH hρ2]

/-! ## The lower bound -/

/-- **The energy bound at a critical zero.**  For every critical zero `ρ` and `N ≥ 2`,
`1 ≤ d_N² (4|ρ|²(1 + 7 log N) + 4 + 576(12|ρ| + 4)²)`. -/
theorem one_le_bdDistDiscrete_sq_mul_of_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : ρ.re = 1 / 2) {N : ℕ} (hN : 2 ≤ N) :
    1 ≤ bdDistDiscrete N ^ 2 *
      (4 * ‖ρ‖ ^ 2 * (1 + 7 * Real.log N) + 4 + 576 * (12 * ‖ρ‖ + 4) ^ 2) := by
  set Cv : ℝ := 12 * ‖ρ‖ + 4 with hCv
  have hCv0 : 0 ≤ Cv := by positivity
  set Y : ℕ := N ^ 7 with hYdef
  have hN1 : 1 ≤ N := by omega
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hY1 : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY1
  obtain ⟨P, hP, hNP, hP2N⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  have hPY : P ≤ Y := by
    have h1 : 2 * N ≤ N ^ 7 := by
      calc 2 * N ≤ N * N := Nat.mul_le_mul_right N hN
        _ = N ^ 2 := (sq N).symm
        _ ≤ N ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  set v : ℕ → ℂ := fun m => -bdModDefect (zeroDual ρ Y) Y m with hv
  set b : ℕ → ℂ := bdMoebiusCorrection N P v with hb
  set a : ℕ → ℂ := zeroDual ρ Y + b with ha
  set A : ℕ → ℝ := fun k => (a k).re with hA
  -- support, value at one, constraints
  have hAsupp : ∀ k, Y < k → A k = 0 := by
    intro k hk
    simp only [hA, ha, Pi.add_apply]
    have hbk : b k = 0 := bdMoebiusCorrection_eq_zero hNP v (by omega)
    rw [zeroDual_eq_zero hk, hbk]
    simp
  have hA1 : A 1 = 1 := by
    simp only [hA, ha, Pi.add_apply]
    rw [zeroDual_one hY1, hb, bdMoebiusCorrection_one hP.two_le]
    simp
  have hC : ∀ m, 2 ≤ m → m ≤ N →
      ∑ n ∈ (range Y).filter (fun n => m ∣ n + 1), A (n + 1) =
        (1 / (m : ℝ)) * ∑ n ∈ range Y, A (n + 1) := by
    intro m hm2 hmN
    refine dual_constraint_re (a := a) ?_
    rw [ha, bdModDefect_add, hb, bdModDefect_bdMoebiusCorrection hP hNP hPY v hm2 hmN, hv]
    ring
  have hmain := one_le_bdDistDiscrete_sq_mul_energy hAsupp hA1 hC
  -- the energy of the zero dual
  have hE0 := bdDualEnergyC_zeroDual_le hre hY1 Y
  have hlogY : Real.log (Y : ℝ) = 7 * Real.log N := by
    rw [hYdef, Nat.cast_pow, Real.log_pow]; norm_num
  rw [hlogY] at hE0
  -- the energy of the correction
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hvb : ∀ m, 1 ≤ m → m ≤ N → ‖v m‖ ≤ Cv * (Real.sqrt Y)⁻¹ := by
    intro m hm1 _
    rw [hv, norm_neg]
    exact norm_bdModDefect_zeroDual_le hρ hre hY1 le_rfl hm1
  have hV : ∑ m ∈ Icc 2 N, ‖v m‖ ≤ N * (Cv * (Real.sqrt Y)⁻¹) := by
    refine (sum_le_sum fun m hm => hvb m (by simp only [mem_Icc] at hm; omega)
      (mem_Icc.mp hm).2).trans ?_
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast (by omega : N + 1 - 2 ≤ N)
  have hbB : ∀ k, ‖b k‖ ≤ ((N : ℝ) + 1) * (N * (Cv * (Real.sqrt Y)⁻¹)) := by
    intro k
    refine (norm_bdMoebiusCorrection_le N P v k).trans ?_
    exact mul_le_mul_of_nonneg_left hV (by positivity)
  have hEb := bdDualEnergyC_le_of_bounded (K := Y)
    (fun k hk => bdMoebiusCorrection_eq_zero hNP v hk) hbB
  have hEb' : bdDualEnergyC b Y ≤ 288 * Cv ^ 2 := by
    refine hEb.trans ?_
    have hPR : (P : ℝ) ≤ 2 * N := by exact_mod_cast hP2N
    have hP1 : (P : ℝ) + 1 ≤ 3 * N := by linarith
    have hinvY : ((Real.sqrt Y)⁻¹) ^ 2 = 1 / (N : ℝ) ^ 7 := by
      rw [inv_pow, Real.sq_sqrt hY0.le, hYdef]; push_cast; rw [one_div]
    have hN0 : (0 : ℝ) < N := by linarith
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    calc (P : ℝ) * ((P : ℝ) + 1) ^ 2 * (2 * (((N : ℝ) + 1) * (N * (Cv * (Real.sqrt Y)⁻¹)))) ^ 2
        = (P : ℝ) * ((P : ℝ) + 1) ^ 2 * (4 * ((N : ℝ) + 1) ^ 2 * N ^ 2 * Cv ^ 2) *
            ((Real.sqrt Y)⁻¹) ^ 2 := by ring
      _ ≤ (2 * N) * (3 * N) ^ 2 * (4 * (2 * N) ^ 2 * N ^ 2 * Cv ^ 2) *
            ((Real.sqrt Y)⁻¹) ^ 2 := by
          gcongr
          linarith
      _ = 288 * Cv ^ 2 := by
          rw [hinvY]; field_simp; ring
  have hEa : bdDualEnergyC a Y ≤ 2 * (2 * ‖ρ‖ ^ 2 * (1 + 7 * Real.log N) + 2) +
      2 * (288 * Cv ^ 2) := by
    refine (bdDualEnergyC_add_le _ _ Y).trans ?_
    linarith
  have hEA : bdDualEnergy A Y ≤ 4 * ‖ρ‖ ^ 2 * (1 + 7 * Real.log N) + 4 + 576 * Cv ^ 2 := by
    refine (bdDualEnergy_re_le a Y).trans ?_
    linarith
  have hd0 : 0 ≤ bdDistDiscrete N ^ 2 := sq_nonneg _
  calc (1 : ℝ) ≤ bdDistDiscrete N ^ 2 * bdDualEnergy A Y := hmain
    _ ≤ bdDistDiscrete N ^ 2 * (4 * ‖ρ‖ ^ 2 * (1 + 7 * Real.log N) + 4 + 576 * Cv ^ 2) :=
        mul_le_mul_of_nonneg_left hEA hd0

/-- **The Báez-Duarte distances decay at most like `1/√(log N)`.**  There is `c > 0` with
`d_N² ≥ c/log N` for every `N ≥ 2`.  Unconditional: the dual sequence `k^{−ρ}(1 − (k−1)/Y)` at
one critical zero `ρ`, `Y = N⁷`, annihilates the first `N` generators up to `O(Y^{−1/2})`, and an
exact Möbius correction over the divisor lattice removes the remainder. -/
theorem exists_div_log_le_bdDistDiscrete_sq :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → c / Real.log N ≤ bdDistDiscrete N ^ 2 := by
  obtain ⟨ρ, hre, hρ⟩ := ZetaMultiple.exists_riemannZeta_zero_re_half
  set α : ℝ := 4 * ‖ρ‖ ^ 2 + 4 + 576 * (12 * ‖ρ‖ + 4) ^ 2 with hα
  set β : ℝ := 28 * ‖ρ‖ ^ 2 with hβ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hα0 : 0 < α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  refine ⟨1 / (α / Real.log 2 + β), by positivity, fun N hN => ?_⟩
  have h := one_le_bdDistDiscrete_sq_mul_of_zero hρ hre hN
  have hlogN : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlogN0 : 0 < Real.log N := hl2.trans_le hlogN
  have hE : 4 * ‖ρ‖ ^ 2 * (1 + 7 * Real.log N) + 4 + 576 * (12 * ‖ρ‖ + 4) ^ 2 =
      α + β * Real.log N := by rw [hα, hβ]; ring
  rw [hE] at h
  have hαβ : α + β * Real.log N ≤ (α / Real.log 2 + β) * Real.log N := by
    have : α ≤ α / Real.log 2 * Real.log N := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hlogN hα0.le
    nlinarith
  have hpos : 0 < α + β * Real.log N := by positivity
  rw [div_div, div_le_iff₀ (by positivity)]
  calc (1 : ℝ) ≤ bdDistDiscrete N ^ 2 * (α + β * Real.log N) := h
    _ ≤ bdDistDiscrete N ^ 2 * ((α / Real.log 2 + β) * Real.log N) :=
        mul_le_mul_of_nonneg_left hαβ (sq_nonneg _)

end

end RHTower
