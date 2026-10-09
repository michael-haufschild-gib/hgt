import GaloisForLFunctions.RHTower.MobiusSquareResidueShortBilinear

set_option autoImplicit false
open scoped BigOperators
open Finset ArithmeticFunction

namespace RHTower

/-- The source's scalar and harmonic counterterms placed in the first row and column. -/
noncomputable def mobiusRenormalizedSquareKernel (N a b : ℕ) : ℝ :=
  mobiusSquareShortBilinearKernel N (a * b) -
    (if a = 1 ∧ b = 1 then ∑ s ∈ range N, (s : ℝ) ^ 2 else 0) -
    (if a = 1 then (∑ s ∈ range N, (s : ℝ) ^ 2) * Real.log b / b else 0) -
    (if b = 1 then (∑ s ∈ range N, (s : ℝ) ^ 2) * Real.log a / a else 0)

theorem mobiusRenormalizedSquareKernel_symmetric (N a b : ℕ) :
    mobiusRenormalizedSquareKernel N a b = mobiusRenormalizedSquareKernel N b a := by
  unfold mobiusRenormalizedSquareKernel
  simp only [Nat.mul_comm a b, and_comm]
  ring

theorem mobiusRenormalizedSquareKernel_eq_of_ne_one (N : ℕ) {a b : ℕ}
    (ha : a ≠ 1) (hb : b ≠ 1) :
    mobiusRenormalizedSquareKernel N a b = mobiusSquareShortBilinearKernel N (a * b) := by
  simp [mobiusRenormalizedSquareKernel, ha, hb]

theorem sum_mobiusRenormalizedSquareKernel {N : ℕ} (hN : 1 ≤ N) (f : ℕ → ℝ) :
    (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      f a * f b * mobiusRenormalizedSquareKernel N a b) =
      (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        f a * f b * mobiusSquareShortBilinearKernel N (a * b)) -
      (∑ s ∈ range N, (s : ℝ) ^ 2) * (f 1) ^ 2 -
      2 * (∑ s ∈ range N, (s : ℝ) ^ 2) * f 1 *
        ∑ b ∈ Icc 1 N, f b * Real.log b / b := by
  let Q : ℝ := ∑ s ∈ range N, (s : ℝ) ^ 2
  have hdiag : (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      f a * f b * (if a = 1 ∧ b = 1 then Q else 0)) = Q * (f 1) ^ 2 := by
    have hrow (a : ℕ) : (∑ b ∈ Icc 1 N,
        f a * f b * (if a = 1 ∧ b = 1 then Q else 0)) =
          if a = 1 then (f 1) ^ 2 * Q else 0 := by
      by_cases ha : a = 1 <;> simp [ha, mul_ite, hN, pow_two]
    simp_rw [hrow]
    simp [hN, mul_comm]
  have hleft : (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      f a * f b * (if a = 1 then Q * Real.log b / b else 0)) =
        Q * f 1 * ∑ b ∈ Icc 1 N, f b * Real.log b / b := by
    calc
      _ = ∑ b ∈ Icc 1 N, f 1 * f b * (Q * Real.log b / b) := by
        rw [sum_comm]
        simp [mul_ite, hN]
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro b _
        ring
  have hright : (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      f a * f b * (if b = 1 then Q * Real.log a / a else 0)) =
        Q * f 1 * ∑ a ∈ Icc 1 N, f a * Real.log a / a := by
    calc
      _ = ∑ a ∈ Icc 1 N, f a * f 1 * (Q * Real.log a / a) := by
        simp [mul_ite, hN]
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro a _
        ring
  unfold mobiusRenormalizedSquareKernel
  simp_rw [mul_sub, sum_sub_distrib]
  change _ - (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      f a * f b * (if a = 1 ∧ b = 1 then Q else 0)) -
    (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      f a * f b * (if a = 1 then Q * Real.log b / b else 0)) -
    (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
      f a * f b * (if b = 1 then Q * Real.log a / a else 0)) = _
  rw [hdiag, hleft, hright]
  dsimp only [Q]
  ring

/-- This matrix represents the actual short source, with its full counterterm retained. -/
theorem mobiusShortBilinearSquareSource_eq_renormalized {N : ℕ} (hN : 1 ≤ N) :
    mobiusShortBilinearSquareSource N =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        (moebius a : ℝ) * (moebius b : ℝ) * mobiusRenormalizedSquareKernel N a b := by
  rw [sum_mobiusRenormalizedSquareKernel hN]
  have hmu : (moebius 1 : ℝ) = 1 := by simp
  rw [hmu]
  unfold mobiusShortBilinearSquareSource logMobiusShortBilinearSquareAction
  ring

private theorem square_renormalized_cross_pos {N : ℕ} (hN : 4 ≤ N) :
    0 < mobiusSquareShortBilinearKernel N (2 * N) := by
  have hp : N - 1 + 1 = N := by omega
  have hm := Nat.mul_le_mul_left (N - 1) (show 3 ≤ N - 1 by omega)
  have hcut : 2 * N ≤ (N - 1) ^ 2 := by nlinarith
  exact (mobiusSquareShortBilinearKernel_pos_iff (by omega) (by omega)).mpr hcut

/-- Every correction supported in the first row or column leaves this negative minor. -/
theorem squareKernel_firstRowCorrection_minor_neg {N : ℕ} (hN : 4 ≤ N)
    (R : ℕ → ℕ → ℝ)
    (hR : ∀ a b : ℕ, a ≠ 1 → b ≠ 1 → R a b = mobiusSquareShortBilinearKernel N (a * b)) :
    R 2 2 * R N N - (R 2 N) ^ 2 < 0 := by
  rw [hR N N (by omega) (by omega), ← pow_two,
    mobiusSquareShortBilinearKernel_terminal_zero, mul_zero,
    hR 2 N (by omega) (by omega)]
  have hp := square_renormalized_cross_pos hN
  have hs : 0 < mobiusSquareShortBilinearKernel N (2 * N) ^ 2 := by
    simpa only [pow_two] using mul_pos hp hp
  linarith

theorem mobiusRenormalizedSquareKernel_terminal_zero {N : ℕ} (hN : 2 ≤ N) :
    mobiusRenormalizedSquareKernel N N N = 0 := by
  rw [mobiusRenormalizedSquareKernel_eq_of_ne_one N (by omega) (by omega), ← pow_two]
  exact mobiusSquareShortBilinearKernel_terminal_zero N

/-- The onset of indefiniteness in the two-coordinate block is exactly N = 4. -/
theorem mobiusRenormalizedSquareKernel_minor_neg_iff {N : ℕ} (hN : 2 ≤ N) :
    mobiusRenormalizedSquareKernel N 2 2 * mobiusRenormalizedSquareKernel N N N -
        (mobiusRenormalizedSquareKernel N 2 N) ^ 2 < 0 ↔ 4 ≤ N := by
  constructor
  · intro h
    by_contra h4
    have hp : N - 1 + 1 = N := by omega
    have hm := Nat.mul_le_mul_left (N - 1) (show N - 1 ≤ 2 by omega)
    have hcut : (N - 1) ^ 2 < 2 * N := by nlinarith
    have hz : mobiusRenormalizedSquareKernel N 2 N = 0 := by
      rw [mobiusRenormalizedSquareKernel_eq_of_ne_one N (by omega) (by omega)]
      exact mobiusSquareShortBilinearKernel_eq_zero_of_cutoff hcut
    rw [mobiusRenormalizedSquareKernel_terminal_zero hN, hz] at h
    norm_num at h
  · intro h4
    exact squareKernel_firstRowCorrection_minor_neg h4 (mobiusRenormalizedSquareKernel N)
      (fun a b ha hb => mobiusRenormalizedSquareKernel_eq_of_ne_one N ha hb)

/-- An explicit negative direction, independent of the first coordinate. -/
theorem mobiusRenormalizedSquareKernel_negative_direction {N : ℕ} (hN : 4 ≤ N) :
    mobiusRenormalizedSquareKernel N 2 2 +
      2 * (-(mobiusRenormalizedSquareKernel N 2 2 + 1) /
        (2 * mobiusRenormalizedSquareKernel N 2 N)) * mobiusRenormalizedSquareKernel N 2 N +
      (-(mobiusRenormalizedSquareKernel N 2 2 + 1) /
        (2 * mobiusRenormalizedSquareKernel N 2 N)) ^ 2 *
          mobiusRenormalizedSquareKernel N N N = -1 := by
  have hp : 0 < mobiusRenormalizedSquareKernel N 2 N := by
    rw [mobiusRenormalizedSquareKernel_eq_of_ne_one N (by omega) (by omega)]
    exact square_renormalized_cross_pos hN
  rw [mobiusRenormalizedSquareKernel_terminal_zero (by omega), mul_zero, add_zero]
  field_simp [ne_of_gt hp]
  ring

private theorem square_renormalized_six_mul_moment (N : ℕ) :
    6 * (∑ s ∈ range N, (s : ℝ) ^ 2) = (N : ℝ) * ((N : ℝ) - 1) * (2 * N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith only [ih]

private theorem square_renormalized_floor_four_lower {N : ℕ} (hN : 8 ≤ N) :
    (N : ℝ) ^ 3 / 64 ≤ mobiusSquareFloorPrefix N 4 := by
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hmoment := square_renormalized_six_mul_moment N
  have hfac : 0 ≤ (N : ℝ) * ((N : ℝ) - 2) * (5 * N - 2) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (by linarith)) (by linarith)
  have hQ : (N : ℝ) ^ 3 / 8 ≤ ∑ s ∈ range N, (s : ℝ) ^ 2 := by
    nlinarith only [hmoment, hfac]
  have hV : quadraticResiduePrefix N 4 ≤ 4 * (N : ℝ) := by
    unfold quadraticResiduePrefix
    calc
      _ ≤ ∑ _s ∈ range N, (4 : ℝ) := by
        apply sum_le_sum
        intro s _
        exact_mod_cast (Nat.mod_lt (s ^ 2) (by norm_num : 0 < 4)).le
      _ = _ := by simp; ring
  have hdiv := quadraticResiduePrefix_add_mul_floor N 4
  have hcube : 0 ≤ (N : ℝ) * ((N : ℝ) - 8) * ((N : ℝ) + 8) := by positivity
  norm_num only [Nat.cast_ofNat] at hdiv
  nlinarith only [hQ, hV, hdiv, hcube]

/-- A bounded unit coordinate still has cubic positive value after all source counterterms. -/
theorem mobiusRenormalizedSquareKernel_two_diagonal_cubic_lower {N : ℕ} (hN : 8 ≤ N) :
    Real.log 2 / 32 * (N : ℝ) ^ 3 ≤ mobiusRenormalizedSquareKernel N 2 2 := by
  rw [mobiusRenormalizedSquareKernel_eq_of_ne_one N (by omega) (by omega)]
  have hk : ({1} : Finset ℕ) ⊆ Icc 1 (N ^ 2 / 4) := by
    intro k hk
    have hk1 : k = 1 := mem_singleton.mp hk
    subst k
    exact mem_Icc.mpr ⟨le_rfl, (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by nlinarith)⟩
  have hs := sum_le_sum_of_subset_of_nonneg hk
    (f := fun k => Real.log (4 * k : ℕ) * mobiusSquareFloorPrefix N (4 * k))
    (fun k _ _ => mul_nonneg (Real.log_natCast_nonneg (4 * k))
      (sum_nonneg fun _ _ => Nat.cast_nonneg _))
  have hK : Real.log 4 * mobiusSquareFloorPrefix N 4 ≤ mobiusSquareShortBilinearKernel N 4 := by
    simpa [mobiusSquareShortBilinearKernel] using hs
  have hlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  norm_num only [Nat.reduceMul]
  calc
    _ = Real.log 4 * ((N : ℝ) ^ 3 / 64) := by rw [hlog]; ring
    _ ≤ Real.log 4 * mobiusSquareFloorPrefix N 4 :=
      mul_le_mul_of_nonneg_left (square_renormalized_floor_four_lower hN) (Real.log_nonneg (by norm_num))
    _ ≤ _ := hK

/-- No coefficient-independent critical upper estimate can hold even on this unit direction. -/
theorem mobiusRenormalizedSquareKernel_two_diagonal_exceeds_quadratic (B : ℝ) :
    ∃ N : ℕ, 8 ≤ N ∧ B * (N : ℝ) ^ 2 < mobiusRenormalizedSquareKernel N 2 2 := by
  let c : ℝ := Real.log 2 / 32
  have hc : 0 < c := by dsimp [c]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 8 (B / c))
  have hNr : (8 : ℝ) ≤ N := (le_max_left _ _).trans hN.le
  have hN8 : 8 ≤ N := by exact_mod_cast hNr
  have hb : B / c < (N : ℝ) := (le_max_right _ _).trans_lt hN
  have hbc : B < c * N := by
    have hh := mul_lt_mul_of_pos_left hb hc
    have he : c * (B / c) = B := by field_simp
    rwa [he] at hh
  have hprod := mul_lt_mul_of_pos_right hbc (show 0 < (N : ℝ) ^ 2 by positivity)
  refine ⟨N, hN8, ?_⟩
  calc
    _ < c * (N : ℝ) ^ 3 := by nlinarith only [hprod]
    _ ≤ _ := mobiusRenormalizedSquareKernel_two_diagonal_cubic_lower hN8

theorem mobiusRenormalizedSquareKernel_two_diagonal_pos {N : ℕ} (hN : 3 ≤ N) :
    0 < mobiusRenormalizedSquareKernel N 2 2 := by
  rw [mobiusRenormalizedSquareKernel_eq_of_ne_one N (by omega) (by omega)]
  norm_num only [Nat.reduceMul]
  apply (mobiusSquareShortBilinearKernel_pos_iff (by omega) (by omega)).mpr
  have h := Nat.mul_le_mul (show 2 ≤ N - 1 by omega) (show 2 ≤ N - 1 by omega)
  simpa only [pow_two] using h

/-- The full two-coordinate quadratic form is nonnegative exactly before N = 4. -/
theorem mobiusRenormalizedSquareKernel_plane_nonnegative_iff {N : ℕ} (hN : 2 ≤ N) :
    (∀ x y : ℝ, 0 ≤ x ^ 2 * mobiusRenormalizedSquareKernel N 2 2 +
      2 * x * y * mobiusRenormalizedSquareKernel N 2 N +
      y ^ 2 * mobiusRenormalizedSquareKernel N N N) ↔ N ≤ 3 := by
  constructor
  · intro h
    by_contra hn
    have h4 : 4 ≤ N := by omega
    let y : ℝ := -(mobiusRenormalizedSquareKernel N 2 2 + 1) /
      (2 * mobiusRenormalizedSquareKernel N 2 N)
    have h0 := h 1 y
    simp only [one_pow, one_mul, mul_one] at h0
    have he : mobiusRenormalizedSquareKernel N 2 2 +
        2 * y * mobiusRenormalizedSquareKernel N 2 N +
        y ^ 2 * mobiusRenormalizedSquareKernel N N N = -1 :=
      mobiusRenormalizedSquareKernel_negative_direction h4
    rw [he] at h0
    norm_num at h0
  · intro hn x y
    have hp : N - 1 + 1 = N := by omega
    have hm := Nat.mul_le_mul_left (N - 1) (show N - 1 ≤ 2 by omega)
    have hcut : (N - 1) ^ 2 < 2 * N := by nlinarith
    have hz : mobiusRenormalizedSquareKernel N 2 N = 0 := by
      rw [mobiusRenormalizedSquareKernel_eq_of_ne_one N (by omega) (by omega)]
      exact mobiusSquareShortBilinearKernel_eq_zero_of_cutoff hcut
    have hd : 0 ≤ mobiusRenormalizedSquareKernel N 2 2 := by
      rw [mobiusRenormalizedSquareKernel_eq_of_ne_one N (by omega) (by omega)]
      exact mobiusSquareShortBilinearKernel_nonneg N _
    rw [hz, mobiusRenormalizedSquareKernel_terminal_zero hN]
    simpa only [mul_zero, add_zero] using mul_nonneg (sq_nonneg x) hd

end RHTower
