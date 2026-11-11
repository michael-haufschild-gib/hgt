import GaloisForLFunctions.RHTower.ZetaTypicalHeightSup
import GaloisForLFunctions.HTGeometry.PowerMomentsFromDyadicMass

/-!
# Square mass of zeta in unit height cells

The area mean-value inequality controls local values by the square mass of
the pole-cleared zeta function in a box. Summing the boxes costs only their
bounded overlap; vertical mean squares then give the dyadic growth bound.
-/

noncomputable section

open Complex Set MeasureTheory Finset

namespace RHTower

/-- Square mass of the pole-cleared zeta function in the box around one height cell. -/
def zetaUnitCellSquareMass (r t : ℝ) : ℝ :=
  ∫ x in (1 / 2 - r)..(5 / 2),
    ∫ y in (t - 3)..(t + 4), ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2

theorem zetaUnitCellSquareMass_nonneg {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    0 ≤ zetaUnitCellSquareMass r t :=
  intervalIntegral.integral_nonneg (by linarith only [hr]) fun x _ =>
    intervalIntegral.integral_nonneg (by linarith) fun y _ => sq_nonneg _

/-- Bounded overlap converts the vertical second moment into a sum over cells. -/
theorem sum_zetaUnitCellSquareMass_le {C K r : ℝ}
    (hC : 0 < C) (hK : 0 ≤ K) (hr0 : 0 < r) (hr : r ≤ 1 / 4)
    (hmean : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 →
      ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C * T * (1 + Real.log T) ^ 3)
    (hχ : ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 4 → ∀ t : ℝ,
      ‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ K * (max 1 |t|) ^ d)
    {T : ℝ} (hT : 6 ≤ T) {m : ℕ} (hm : (m : ℝ) ≤ T + 2) :
    ∑ k ∈ range m, zetaUnitCellSquareMass r (T + k) ≤
      21 * ((4 * T + 2) ^ 2 * ((K * (4 * T) ^ r) ^ 2 + 1) *
        (4 * C * T * (1 + Real.log (4 * T)) ^ 3)) := by
  let Q := (4 * T + 2) ^ 2 * ((K * (4 * T) ^ r) ^ 2 + 1) *
    (4 * C * T * (1 + Real.log (4 * T)) ^ 3)
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ 1 + Real.log (4 * T) := by
      linarith only [Real.log_nonneg (by linarith only [hT] : (1 : ℝ) ≤ 4 * T)]
    dsimp [Q]
    positivity
  have hswap : ∑ k ∈ range m, zetaUnitCellSquareMass r (T + k) =
      ∫ x in (1 / 2 - r)..(5 / 2), ∑ k ∈ range m,
        ∫ y in (T + k - 3)..(T + k + 4), ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
    rw [intervalIntegral.integral_finsetSum]
    · rfl
    · intro k _
      exact (continuous_integral_normSq_zetaEntire_column (by linarith)).intervalIntegrable _ _
  rw [hswap]
  have hpt : ∀ x ∈ uIoc (1 / 2 - r) (5 / 2),
      ‖∑ k ∈ range m, ∫ y in (T + k - 3)..(T + k + 4),
        ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2‖ ≤ 7 * Q := by
    intro x hx
    rw [uIoc_of_le (by linarith only [hr0])] at hx
    have hg : Continuous fun y : ℝ => ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
      (differentiable_zetaEntire.continuous.comp (by fun_prop)).norm.pow 2
    have hsl := sum_integral_sliding_le hg (fun y => sq_nonneg _) T m
    have hcol := integral_normSq_zetaEntire_column_le hC hK hr0 hr hmean hχ
      (T := T) (x := x) (Y₁ := T - 3) (Y₂ := T + m + 4)
      (by linarith only [hT]) hx.1.le hx.2
      (by linarith only [hT])
      (by have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith only [hm0])
      (by linarith only [hT, hm])
    have hnonneg : 0 ≤ ∑ k ∈ range m,
        ∫ y in (T + k - 3)..(T + k + 4), ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
      sum_nonneg fun k _ => intervalIntegral.integral_nonneg (by linarith) fun y _ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hsl.trans (mul_le_mul_of_nonneg_left hcol (by norm_num))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_pos (by linarith only [hr0])] at hnorm
  calc
    _ ≤ ‖∫ x in (1 / 2 - r)..(5 / 2), ∑ k ∈ range m,
        ∫ y in (T + k - 3)..(T + k + 4), ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2‖ :=
      Real.le_norm_self _
    _ ≤ 7 * Q * (5 / 2 - (1 / 2 - r)) := hnorm
    _ ≤ 21 * Q := by
      have hprod := mul_le_mul_of_nonneg_right hr hQ
      nlinarith only [hprod, hQ]

/-- Every positive loss permits a thin strip whose cell masses grow at
most like `T^(3+ε)` on dyadic blocks. -/
theorem exists_zetaUnitCellSquareMass_dyadic_bound {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ r > 0, r ≤ 1 / 4 ∧ ∃ B > 0, ∀ j : ℕ, 3 ≤ j →
      ∑ n ∈ Finset.Ioc ((2 : ℕ) ^ j) (2 ^ (j + 1)), zetaUnitCellSquareMass r n ≤
        B * ((2 : ℝ) ^ j) ^ (3 + ε) := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_zeta_vertical_le
  obtain ⟨K, hK, hχ⟩ :=
    exists_norm_zetaChi_moving_left_line_le_rpow (d₀ := 1 / 4) (by norm_num) (by norm_num)
  let c := 100 * C * (K ^ 2 + 1) * (1 + 12 / ε) ^ 3
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨ε / 4, by positivity, by linarith only [hε1],
    21 * c * (4 : ℝ) ^ ε, by positivity, fun j hj => ?_⟩
  let N : ℕ := 2 ^ j
  let T : ℝ := (2 : ℝ) ^ j
  have hNT : (N : ℝ) = T := by simp only [N, T, Nat.cast_pow, Nat.cast_ofNat]
  have hT : 8 ≤ T := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
    norm_num at h
    exact h
  have hT0 : 0 < T := by linarith only [hT]
  have hsum := sum_zetaUnitCellSquareMass_le hC hK (by positivity : 0 < ε / 4)
    (by linarith only [hε1]) hmean (fun d hd0 hd t => hχ d hd0 hd t)
    (T := T) (m := N + 1) (by linarith only [hT]) (by rw [Nat.cast_add, Nat.cast_one, hNT]; linarith)
  have hblock : ∑ n ∈ Finset.Ioc ((2 : ℕ) ^ j) (2 ^ (j + 1)), zetaUnitCellSquareMass (ε / 4) n ≤
      ∑ k ∈ range (N + 1), zetaUnitCellSquareMass (ε / 4) (T + k) := by
    calc
      _ ≤ ∑ n ∈ Ico N (2 * N + 1), zetaUnitCellSquareMass (ε / 4) n :=
        sum_le_sum_of_subset_of_nonneg (by
          intro n hn
          rw [Finset.mem_Ioc, show (2 : ℕ) ^ (j + 1) = 2 * N by dsimp [N]; ring] at hn
          exact Finset.mem_Ico.mpr ⟨hn.1.le, by omega⟩)
          (fun n _ _ => zetaUnitCellSquareMass_nonneg (by positivity) n)
      _ = ∑ k ∈ range (N + 1), zetaUnitCellSquareMass (ε / 4) (T + k) := by
        rw [sum_Ico_eq_sum_range, show 2 * N + 1 - N = N + 1 by omega]
        simp only [Nat.cast_add, hNT]
  obtain ⟨hu1, hr3, hlog, _⟩ :=
    zetaLargeNear_scale_bounds (T := T) hε hε1 (by linarith only [hT])
  let u := (4 * T) ^ (ε / 12)
  have hlog0 : 0 ≤ 1 + Real.log (4 * T) := by
    linarith only [Real.log_nonneg (by linarith only [hT] : (1 : ℝ) ≤ 4 * T)]
  have hpoly : (4 * T + 2) ^ 2 ≤ 25 * T ^ 2 := by nlinarith only [hT]
  have hK' : (K * u ^ 3) ^ 2 + 1 ≤ (K ^ 2 + 1) * u ^ 6 := by
    have hu6 : 1 ≤ u ^ 6 := one_le_pow₀ hu1
    nlinarith only [hu6, sq_nonneg K]
  have hlog' : (1 + Real.log (4 * T)) ^ 3 ≤ (1 + 12 / ε) ^ 3 * u ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlog0 hlog 3
  have hQ : (4 * T + 2) ^ 2 * ((K * (4 * T) ^ (ε / 4)) ^ 2 + 1) *
      (4 * C * T * (1 + Real.log (4 * T)) ^ 3) ≤ c * T ^ 3 * u ^ 9 := by
    rw [hr3]
    calc
      _ ≤ (25 * T ^ 2) * ((K ^ 2 + 1) * u ^ 6) *
          (4 * C * T * ((1 + 12 / ε) ^ 3 * u ^ 3)) := by
        gcongr
      _ = c * T ^ 3 * u ^ 9 := by dsimp [c]; ring
  have hu9 : u ^ 9 ≤ (4 * T) ^ ε := by
    rw [show u ^ 9 = (4 * T) ^ ((ε / 12) * 9) by
      dsimp [u]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hT])
      (by linarith only [hε])
  calc
    _ ≤ 21 * (c * T ^ 3 * u ^ 9) :=
      hblock.trans (hsum.trans (mul_le_mul_of_nonneg_left hQ (by norm_num)))
    _ ≤ 21 * (c * T ^ 3 * (4 * T) ^ ε) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu9 (by positivity)) (by norm_num)
    _ = (21 * c * (4 : ℝ) ^ ε) * T ^ (3 + ε) := by
      rw [Real.mul_rpow (by norm_num) hT0.le, Real.rpow_add hT0,
        ← Real.rpow_natCast]
      norm_num <;> ring

/-- A sufficiently thin strip has every square-mass moment strictly above three. -/
theorem exists_summable_zetaUnitCellSquareMass_div_rpow {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ r > 0, r ≤ 1 / 4 ∧
      Summable (fun n : ℕ => zetaUnitCellSquareMass r n / (n : ℝ) ^ (3 + ε)) := by
  obtain ⟨r, hr, hr4, B, _, hblock⟩ :=
    exists_zetaUnitCellSquareMass_dyadic_bound (ε := ε / 2)
      (by positivity) (by linarith only [hε1])
  exact ⟨r, hr, hr4, GaloisForLFunctions.HTGeometry.summable_div_rpow_of_dyadic_mass_bound
    (fun n => zetaUnitCellSquareMass_nonneg hr.le n)
    (by linarith only [hε] : 0 ≤ 3 + ε / 2)
    (by linarith only [hε] : 3 + ε / 2 < 3 + ε) hblock⟩

/-- Normalized square-root cell masses have every moment between one and two. -/
theorem exists_summable_zetaUnitCellEnvelope_rpow {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    ∃ r > 0, r ≤ 1 / 4 ∧
      Summable (fun n : ℕ => (Real.sqrt (zetaUnitCellSquareMass r n) / (n : ℝ) ^ 2) ^ q) := by
  have hq : 0 < q := zero_lt_one.trans hq1
  let ε := (q - 1) / q
  have hε : 0 < ε := div_pos (sub_pos.mpr hq1) hq
  have hε1 : ε ≤ 1 := (div_le_iff₀ hq).mpr (by linarith)
  have heq : ε * q = q - 1 := div_mul_cancel₀ _ hq.ne'
  obtain ⟨r, hr, hr4, hmoment⟩ := exists_summable_zetaUnitCellSquareMass_div_rpow hε hε1
  exact ⟨r, hr, hr4, GaloisForLFunctions.HTGeometry.summable_sqrt_div_sq_rpow_of_weighted_moment
    (fun n => zetaUnitCellSquareMass_nonneg hr.le n)
    (by linarith only [hε] : 0 < 3 + ε) hq hq2
    (by nlinarith only [heq, hq1] : (3 + ε - 4) * q < q - 2) hmoment⟩

end RHTower
