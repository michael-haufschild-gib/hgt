import GaloisForLFunctions.RHTower.SquareResidueQuadraticCompletion
import GaloisForLFunctions.RHTower.RootOfUnityIntervalCompletion

/-!
Incomplete quadratic Gauss sums for arbitrary positive modulus.
Finite Fourier completion, the multiplication-kernel gcd count, and the
corpus's reciprocal root-of-unity chord estimate give the uniform bound
`sqrt (q * gcd q (2 * a).val) * (2 + log q)` on intervals of length at most
`q`. Even moduli and non-coprime coefficients are included. The underlying
completion identity and geometric bounds also hold for arbitrary lengths.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset Complex

namespace RHTower
variable {q : ℕ} [NeZero q]

noncomputable def squareResidueQuadraticPrefix (a : ZMod q) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, ZMod.stdAddChar (a * (n : ZMod q) ^ 2)

noncomputable def squareResidueLinearPrefix (b : ZMod q) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, ZMod.stdAddChar (-b * (n : ZMod q))

theorem squareResidueQuadraticGaussSum_point_inversion (a y : ZMod q) :
    (q : ℂ) * ZMod.stdAddChar (a * y ^ 2) =
      ∑ b : ZMod q, squareResidueQuadraticGaussSum a b * ZMod.stdAddChar (-b * y) := by
  have h := squareResidueQuadraticGaussSum_completion
    (fun x => if x = y then 1 else 0) a
  simpa [squareResidueFourierCoeff, mul_comm] using h

theorem squareResidueQuadraticPrefix_completion (a : ZMod q) (N : ℕ) :
    (q : ℂ) * squareResidueQuadraticPrefix a N =
      ∑ b : ZMod q, squareResidueQuadraticGaussSum a b * squareResidueLinearPrefix b N := by
  calc
    _ = ∑ n ∈ range N, (q : ℂ) * ZMod.stdAddChar (a * (n : ZMod q) ^ 2) := by
      rw [squareResidueQuadraticPrefix, mul_sum]
    _ = ∑ n ∈ range N, ∑ b : ZMod q,
        squareResidueQuadraticGaussSum a b * ZMod.stdAddChar (-b * (n : ZMod q)) := by
      apply sum_congr rfl
      intro n _
      exact squareResidueQuadraticGaussSum_point_inversion a n
    _ = _ := by
      rw [sum_comm]
      simp only [squareResidueLinearPrefix, mul_sum]

theorem squareResidueLinearPrefix_geometric (b : ZMod q) (N : ℕ) :
    (1 - ZMod.stdAddChar (-b)) * squareResidueLinearPrefix b N =
      1 - ZMod.stdAddChar (-b * (N : ZMod q)) := by
  induction N with
  | zero => simp [squareResidueLinearPrefix, AddChar.map_zero_eq_one]
  | succ N ih =>
    have hstep : ZMod.stdAddChar (-b * ((N + 1 : ℕ) : ZMod q)) =
        ZMod.stdAddChar (-b * (N : ZMod q)) * ZMod.stdAddChar (-b) := by
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, AddChar.map_add_eq_mul]
    rw [squareResidueLinearPrefix, Finset.sum_range_succ, mul_add]
    change (1 - ZMod.stdAddChar (-b)) * squareResidueLinearPrefix b N + _ = _
    rw [ih, hstep]
    ring

theorem norm_squareResidueLinearPrefix_le_length (b : ZMod q) (N : ℕ) :
    ‖squareResidueLinearPrefix b N‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ range N, ‖ZMod.stdAddChar (-b * (n : ZMod q))‖ := norm_sum_le _ _
    _ = _ := by simp [ZMod.stdAddChar_apply]

theorem norm_squareResidueLinearPrefix_mul_le_two (b : ZMod q) (N : ℕ) :
    ‖1 - ZMod.stdAddChar (-b)‖ * ‖squareResidueLinearPrefix b N‖ ≤ 2 := by
  rw [← norm_mul, squareResidueLinearPrefix_geometric]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar (-b * (N : ZMod q))‖ := norm_sub_le _ _
    _ = _ := by norm_num [ZMod.stdAddChar_apply]

theorem norm_squareResidueLinearPrefix_le_cap (b : ZMod q) (N : ℕ) :
    ‖squareResidueLinearPrefix b N‖ ≤
      if b = 0 then (N : ℝ)
      else min (N : ℝ) (2 / ‖1 - ZMod.stdAddChar (-b)‖) := by
  split_ifs with hb
  · exact norm_squareResidueLinearPrefix_le_length b N
  · apply le_min (norm_squareResidueLinearPrefix_le_length b N)
    have hχ : ZMod.stdAddChar (-b) ≠ 1 := by
      intro h
      have h0 : ZMod.stdAddChar (-b) = ZMod.stdAddChar (0 : ZMod q) := by
        simpa only [AddChar.map_zero_eq_one] using h
      exact hb (neg_eq_zero.mp (ZMod.injective_stdAddChar h0))
    have hd : 0 < ‖1 - ZMod.stdAddChar (-b)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hχ))
    apply (le_div_iff₀ hd).mpr
    simpa only [mul_comm] using norm_squareResidueLinearPrefix_mul_le_two b N

theorem norm_squareResidueQuadraticPrefix_le_completion (a : ZMod q) (N : ℕ) :
    (q : ℝ) * ‖squareResidueQuadraticPrefix a N‖ ≤
      Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) *
        ∑ b : ZMod q, ‖squareResidueLinearPrefix b N‖ := by
  calc
    _ = ‖∑ b : ZMod q,
        squareResidueQuadraticGaussSum a b * squareResidueLinearPrefix b N‖ := by
      have h := congrArg (fun z : ℂ => ‖z‖) (squareResidueQuadraticPrefix_completion a N)
      simpa only [norm_mul, Complex.norm_natCast] using h
    _ ≤ ∑ b : ZMod q,
        ‖squareResidueQuadraticGaussSum a b * squareResidueLinearPrefix b N‖ := norm_sum_le _ _
    _ ≤ ∑ b : ZMod q, Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) *
        ‖squareResidueLinearPrefix b N‖ := by
      apply sum_le_sum
      intro b _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_squareResidueQuadraticGaussSum_le_gcd a b)
        (norm_nonneg _)
    _ = _ := by rw [mul_sum]

theorem norm_squareResidueQuadraticPrefix_le_geometric (a : ZMod q) (N : ℕ) :
    (q : ℝ) * ‖squareResidueQuadraticPrefix a N‖ ≤
      Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) *
        ∑ b : ZMod q, if b = 0 then (N : ℝ)
          else min (N : ℝ) (2 / ‖1 - ZMod.stdAddChar (-b)‖) := by
  apply (norm_squareResidueQuadraticPrefix_le_completion a N).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact sum_le_sum fun b _ => norm_squareResidueLinearPrefix_le_cap b N

theorem squareResidue_sum_reciprocalChord_le :
    (∑ b : ZMod q, 2 / ‖1 - ZMod.stdAddChar b‖) ≤
      (q : ℝ) * (1 + Real.log q) := by
  have hchar (b : ZMod q) : ZMod.stdAddChar b =
      Complex.exp (2 * Real.pi * Complex.I * (b.val : ℂ) / q) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      (ZMod.stdAddChar_coe (N := q) (b.val : ℤ))
  have hfilter : (∑ b : ZMod q, 2 / ‖1 - ZMod.stdAddChar b‖) =
      ∑ b ∈ univ.filter (fun b : ZMod q => b ≠ 0), 2 / ‖1 - ZMod.stdAddChar b‖ := by
    rw [sum_filter]
    apply sum_congr rfl
    intro b _
    by_cases hb : b = 0
    · simp [hb, AddChar.map_zero_eq_one]
    · simp [hb]
  have hsum : (∑ b ∈ univ.filter (fun b : ZMod q => b ≠ 0),
        2 / ‖1 - ZMod.stdAddChar b‖) =
      ∑ j ∈ Ioo 0 q, 2 / ‖Complex.exp (2 * Real.pi * Complex.I * j / q) - 1‖ := by
    apply Finset.sum_bij (fun b _ => b.val)
    · intro b hb
      refine mem_Ioo.mpr ⟨Nat.pos_of_ne_zero ?_, ZMod.val_lt b⟩
      intro hv
      exact (mem_filter.mp hb).2 ((ZMod.val_eq_zero b).mp hv)
    · intro a _ b _ he
      have hcast := congrArg (fun n : ℕ => (n : ZMod q)) he
      simpa only [ZMod.natCast_zmod_val] using hcast
    · intro j hj
      have hval : (j : ZMod q).val = j := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_Ioo.mp hj).2]
      refine ⟨(j : ZMod q), ?_, hval⟩
      simp only [mem_filter, mem_univ, true_and]
      intro hz
      have h0 : j = 0 := by simpa only [hz, ZMod.val_zero] using hval.symm
      exact (Nat.ne_of_gt (mem_Ioo.mp hj).1) h0
    · intro b _
      rw [hchar, norm_sub_rev]
  rw [hfilter, hsum]
  exact GaloisForLFunctions.RHTower.RootOfUnityCompletion.sum_two_div_norm_exp_sub_one_le q

theorem sum_norm_squareResidueLinearPrefix_le (N : ℕ) :
    (∑ b : ZMod q, ‖squareResidueLinearPrefix b N‖) ≤
      N + (q : ℝ) * (1 + Real.log q) := by
  have hneg (b : ZMod q) : ‖1 - ZMod.stdAddChar (-b)‖ = ‖1 - ZMod.stdAddChar b‖ := by
    rw [AddChar.map_neg_eq_conj]
    have he : (1 : ℂ) - (starRingEnd ℂ) (ZMod.stdAddChar b) =
        (starRingEnd ℂ) (1 - ZMod.stdAddChar b) := by rw [map_sub, map_one]
    rw [he, Complex.norm_conj]
  calc
    _ ≤ ∑ b : ZMod q, ((if b = 0 then (N : ℝ) else 0) +
        2 / ‖1 - ZMod.stdAddChar b‖) := by
      apply sum_le_sum
      intro b _
      have h := norm_squareResidueLinearPrefix_le_cap b N
      by_cases hb : b = 0
      · simpa [hb, AddChar.map_zero_eq_one] using h
      · simp only [if_neg hb, zero_add, hneg] at h ⊢
        exact h.trans (min_le_right _ _)
    _ = N + ∑ b : ZMod q, 2 / ‖1 - ZMod.stdAddChar b‖ := by
      rw [sum_add_distrib]
      simp
    _ ≤ _ := by
      have h := squareResidue_sum_reciprocalChord_le (q := q)
      linarith

/-- Incomplete quadratic Gauss bound, valid for even and non-coprime moduli. -/
theorem norm_squareResidueQuadraticPrefix_le_log (a : ZMod q) {N : ℕ} (hN : N ≤ q) :
    ‖squareResidueQuadraticPrefix a N‖ ≤
      Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) * (2 + Real.log q) := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hN' : (N : ℝ) ≤ q := by exact_mod_cast hN
  have hscaled : (q : ℝ) * ‖squareResidueQuadraticPrefix a N‖ ≤
      (q : ℝ) * (Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) *
        (2 + Real.log q)) := by
    calc
      _ ≤ Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) *
          ∑ b : ZMod q, ‖squareResidueLinearPrefix b N‖ :=
        norm_squareResidueQuadraticPrefix_le_completion a N
      _ ≤ Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) *
          (N + (q : ℝ) * (1 + Real.log q)) :=
        mul_le_mul_of_nonneg_left (sum_norm_squareResidueLinearPrefix_le N) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt ((q : ℝ) * Nat.gcd q (2 * a).val) *
          ((q : ℝ) + (q : ℝ) * (1 + Real.log q)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)
      _ = _ := by ring
  by_contra h
  have hpos := mul_pos hq (sub_pos.mpr (lt_of_not_ge h))
  nlinarith

end RHTower
