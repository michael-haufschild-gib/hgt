import GaloisForLFunctions.RHTower.SquareResidueQuadraticInterval
import GaloisForLFunctions.RHTower.MobiusSquareResidueDecomposition

/-!
Finite Fourier decomposition of the actual least-square-residue prefix.
The least-residue observable has mean `(q - 1) / 2`; its nonzero Fourier
coefficients have exact norm `q / norm (1 - stdAddChar (-a))`.
The arbitrary-modulus Gauss estimate controls the centered prefix by an
explicit gcd-weighted chord sum. The exact period decomposition extends
this control to every prefix length and retains complete-period bias.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset Complex

namespace RHTower
variable {q : ℕ} [NeZero q]

noncomputable def leastResidueFourierCoeff (a : ZMod q) : ℂ :=
  squareResidueFourierCoeff (fun x : ZMod q => (x.val : ℂ)) a

private theorem squareResidue_sum_zmod_natCast (f : ZMod q → ℂ) :
    (∑ x : ZMod q, f x) = ∑ n ∈ range q, f (n : ZMod q) := by
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x _
    exact mem_range.mpr (ZMod.val_lt x)
  · intro x _ y _ h
    have hc := congrArg (fun n : ℕ => (n : ZMod q)) h
    simpa only [ZMod.natCast_zmod_val] using hc
  · intro n hn
    refine ⟨(n : ZMod q), mem_univ _, ?_⟩
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hn)]
  · intro x _
    rw [ZMod.natCast_zmod_val]

theorem leastResidueFourierCoeff_eq_sum_range (a : ZMod q) :
    leastResidueFourierCoeff a =
      ∑ n ∈ range q, (n : ℂ) * ZMod.stdAddChar (-a * (n : ZMod q)) := by
  rw [leastResidueFourierCoeff, squareResidueFourierCoeff, squareResidue_sum_zmod_natCast]
  apply sum_congr rfl
  intro n hn
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hn)]

private theorem squareResidue_sum_natCast_twice (N : ℕ) :
    2 * (∑ n ∈ range N, (n : ℂ)) = (N : ℂ) * ((N : ℂ) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linear_combination ih

theorem leastResidueFourierCoeff_zero :
    leastResidueFourierCoeff (0 : ZMod q) = (q : ℂ) * ((q : ℂ) - 1) / 2 := by
  rw [leastResidueFourierCoeff_eq_sum_range]
  simp only [neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
  have h := squareResidue_sum_natCast_twice q
  linear_combination h / 2

private theorem squareResidue_geometric_mul (z : ℂ) (N : ℕ) :
    (z - 1) * (∑ n ∈ range N, z ^ n) = z ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linear_combination ih

private theorem squareResidue_weighted_geometric_mul (z : ℂ) (N : ℕ) :
    (z - 1) * (∑ n ∈ range N, (n : ℂ) * z ^ n) =
      (N : ℂ) * z ^ N - z * ∑ n ∈ range N, z ^ n := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ, Nat.cast_succ, pow_succ]
    linear_combination ih

private theorem leastResidue_stdAddChar_ne_one {a : ZMod q} (ha : a ≠ 0) :
    ZMod.stdAddChar (-a) ≠ 1 := by
  intro h
  have h0 : ZMod.stdAddChar (-a) = ZMod.stdAddChar (0 : ZMod q) := by
    simpa only [AddChar.map_zero_eq_one] using h
  exact ha (neg_eq_zero.mp (ZMod.injective_stdAddChar h0))

theorem leastResidueFourierCoeff_mul_character_sub_one {a : ZMod q} (ha : a ≠ 0) :
    (ZMod.stdAddChar (-a) - 1) * leastResidueFourierCoeff a = (q : ℂ) := by
  let z := ZMod.stdAddChar (-a)
  have hp (n : ℕ) : ZMod.stdAddChar (-a * (n : ZMod q)) = z ^ n :=
    GaloisForLFunctions.RHTower.RootOfUnityCompletion.stdAddChar_mul_natCast_pow (-a) n
  have hroot : z ^ q = 1 := by
    rw [← hp q, ZMod.natCast_self, mul_zero, AddChar.map_zero_eq_one]
  have hz : z - 1 ≠ 0 := sub_ne_zero.mpr (leastResidue_stdAddChar_ne_one ha)
  have hg : (∑ n ∈ range q, z ^ n) = 0 := by
    have h := squareResidue_geometric_mul z q
    rw [hroot, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left hz
  rw [leastResidueFourierCoeff_eq_sum_range]
  simp_rw [hp]
  have h := squareResidue_weighted_geometric_mul z q
  simpa only [hroot, hg, mul_one, mul_zero, sub_zero] using h

theorem norm_leastResidueFourierCoeff {a : ZMod q} (ha : a ≠ 0) :
    ‖leastResidueFourierCoeff a‖ = (q : ℝ) / ‖1 - ZMod.stdAddChar (-a)‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖)
    (leastResidueFourierCoeff_mul_character_sub_one ha)
  rw [norm_mul, Complex.norm_natCast, norm_sub_rev] at h
  have hd : ‖1 - ZMod.stdAddChar (-a)‖ ≠ 0 := by
    exact ne_of_gt (norm_pos_iff.mpr
      (sub_ne_zero.mpr (Ne.symm (leastResidue_stdAddChar_ne_one ha))))
  field_simp [hd]
  simpa only [mul_comm] using h

omit [NeZero q] in
private theorem sum_squareResidueVal_eq_prefix (N : ℕ) :
    (∑ n ∈ range N, (((n : ZMod q) ^ 2).val : ℂ)) =
      (quadraticResiduePrefix N q : ℂ) := by
  unfold quadraticResiduePrefix
  push_cast
  apply sum_congr rfl
  intro n _
  congr 1
  rw [← Nat.cast_pow, ZMod.val_natCast]

theorem quadraticResiduePrefix_fourier (N : ℕ) :
    (q : ℂ) * (quadraticResiduePrefix N q : ℂ) =
      ∑ a : ZMod q, leastResidueFourierCoeff a * squareResidueQuadraticPrefix a N := by
  calc
    _ = ∑ n ∈ range N, (q : ℂ) * (((n : ZMod q) ^ 2).val : ℂ) := by
      rw [← sum_squareResidueVal_eq_prefix, mul_sum]
    _ = ∑ n ∈ range N, ∑ a : ZMod q,
        leastResidueFourierCoeff a * ZMod.stdAddChar (a * (n : ZMod q) ^ 2) := by
      apply sum_congr rfl
      intro n _
      exact (squareResidueFourier_inversion (fun x : ZMod q => (x.val : ℂ))
        ((n : ZMod q) ^ 2)).symm
    _ = _ := by
      rw [sum_comm]
      simp only [squareResidueQuadraticPrefix, mul_sum]

theorem quadraticResiduePrefix_centered_fourier (N : ℕ) :
    (q : ℂ) * ((quadraticResiduePrefix N q : ℂ) - (N : ℂ) * ((q : ℂ) - 1) / 2) =
      ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
        leastResidueFourierCoeff a * squareResidueQuadraticPrefix a N := by
  have ht := quadraticResiduePrefix_fourier (q := q) N
  have hs := Finset.sum_erase_add (univ : Finset (ZMod q))
    (fun a => leastResidueFourierCoeff a * squareResidueQuadraticPrefix a N)
    (mem_univ (0 : ZMod q))
  have h0 : leastResidueFourierCoeff (0 : ZMod q) *
      squareResidueQuadraticPrefix (0 : ZMod q) N =
      (q : ℂ) * ((N : ℂ) * ((q : ℂ) - 1) / 2) := by
    rw [leastResidueFourierCoeff_zero]
    simp only [squareResidueQuadraticPrefix, zero_mul, AddChar.map_zero_eq_one,
      sum_const, card_range, nsmul_eq_mul, mul_one]
    ring
  linear_combination ht - hs + h0

theorem abs_quadraticResiduePrefix_centered_le_fourier {N : ℕ} (hN : N ≤ q) :
    |quadraticResiduePrefix N q - (N : ℝ) * ((q : ℝ) - 1) / 2| ≤
      (2 + Real.log q) * ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
        Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) / ‖1 - ZMod.stdAddChar (-a)‖ := by
  have hi : (((q : ℝ) *
      (quadraticResiduePrefix N q - (N : ℝ) * ((q : ℝ) - 1) / 2) : ℝ) : ℂ) =
      ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
        leastResidueFourierCoeff a * squareResidueQuadraticPrefix a N := by
    push_cast
    exact quadraticResiduePrefix_centered_fourier N
  have hn := congrArg (fun z : ℂ => ‖z‖) hi
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg q)] at hn
  have hscaled : (q : ℝ) * |quadraticResiduePrefix N q - (N : ℝ) * ((q : ℝ) - 1) / 2| ≤
      (q : ℝ) * ((2 + Real.log q) * ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
        Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) / ‖1 - ZMod.stdAddChar (-a)‖) := by
    calc
      _ = _ := hn
      _ ≤ ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
          ‖leastResidueFourierCoeff a * squareResidueQuadraticPrefix a N‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
          (q : ℝ) / ‖1 - ZMod.stdAddChar (-a)‖ *
            (Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) * (2 + Real.log q)) := by
        apply sum_le_sum
        intro a ha
        rw [norm_mul, norm_leastResidueFourierCoeff (mem_erase.mp ha).1]
        exact mul_le_mul_of_nonneg_left (norm_squareResidueQuadraticPrefix_le_log a hN)
          (by positivity)
      _ = _ := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro a _
        ring
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  by_contra h
  have hpos := mul_pos hq (sub_pos.mpr (lt_of_not_ge h))
  nlinarith

omit [NeZero q] in
theorem quadraticResiduePrefix_centered_period_decomposition (N : ℕ) :
    quadraticResiduePrefix N q - (N : ℝ) * ((q : ℝ) - 1) / 2 =
      (N / q : ℕ) * (quadraticResiduePrefix q q - (q : ℝ) * ((q : ℝ) - 1) / 2) +
        (quadraticResiduePrefix (N % q) q - (N % q : ℕ) * ((q : ℝ) - 1) / 2) := by
  rw [quadraticResiduePrefix_period_decomposition]
  have hN : (N : ℝ) = (N % q : ℕ) + (q : ℝ) * (N / q : ℕ) := by
    exact_mod_cast (Nat.mod_add_div N q).symm
  rw [hN]
  ring

theorem abs_quadraticResiduePrefix_centered_le_periods (N : ℕ) :
    |quadraticResiduePrefix N q - (N : ℝ) * ((q : ℝ) - 1) / 2| ≤
      ((N / q : ℕ) + 1 : ℝ) * (2 + Real.log q) *
        ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
          Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) / ‖1 - ZMod.stdAddChar (-a)‖ := by
  let B := (2 + Real.log q) * ∑ a ∈ (univ : Finset (ZMod q)).erase 0,
    Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) / ‖1 - ZMod.stdAddChar (-a)‖
  have hfull : |quadraticResiduePrefix q q - (q : ℝ) * ((q : ℝ) - 1) / 2| ≤ B :=
    abs_quadraticResiduePrefix_centered_le_fourier le_rfl
  have hrem : |quadraticResiduePrefix (N % q) q - (N % q : ℕ) * ((q : ℝ) - 1) / 2| ≤ B :=
    abs_quadraticResiduePrefix_centered_le_fourier (Nat.mod_lt N (NeZero.pos q)).le
  rw [quadraticResiduePrefix_centered_period_decomposition]
  calc
    _ ≤ |(N / q : ℕ) *
        (quadraticResiduePrefix q q - (q : ℝ) * ((q : ℝ) - 1) / 2)| +
        |quadraticResiduePrefix (N % q) q - (N % q : ℕ) * ((q : ℝ) - 1) / 2| := abs_add_le _ _
    _ = (N / q : ℕ) * |quadraticResiduePrefix q q - (q : ℝ) * ((q : ℝ) - 1) / 2| +
        |quadraticResiduePrefix (N % q) q - (N % q : ℕ) * ((q : ℝ) - 1) / 2| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (N / q))]
    _ ≤ (N / q : ℕ) * B + B :=
      add_le_add (mul_le_mul_of_nonneg_left hfull (Nat.cast_nonneg _)) hrem
    _ = _ := by dsimp [B]; ring

end RHTower
