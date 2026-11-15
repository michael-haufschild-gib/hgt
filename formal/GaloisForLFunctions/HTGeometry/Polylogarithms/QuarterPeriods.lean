import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicPrimitive
import GaloisForLFunctions.RHTower.EstermannPrincipalPart
import GaloisForLFunctions.RHTower.DQPTPartialSumRate
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Quarter-period factors of classical polylogarithms

At phase `1/4`, sine zeta is the conductor-four quadratic Dirichlet L-function.
The cosine channel is a scalar multiple of Riemann zeta, obtained by subtracting
the two-point distribution formula from the four-point formula. Both channels
are nonzero at every integer weight at least two. Hence the parity-selected
analytic factor in the unit-circle polylogarithm formula is nonzero at `i`.
-/

open Complex HurwitzZeta
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry

private theorem quarterChar_one : ZMod.stdAddChar (1 : ZMod 4) = I := by
  change ZMod.stdAddChar ((1 : ℤ) : ZMod 4) = I
  rw [ZMod.stdAddChar_coe]
  norm_num only [Int.cast_one, Nat.cast_ofNat, mul_one]
  rw [show 2 * (Real.pi : ℂ) * I / 4 = ((Real.pi / 2 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I]
  simp

private theorem quarterChar_two : ZMod.stdAddChar (2 : ZMod 4) = -1 := by
  rw [show (2 : ZMod 4) = 1 + 1 by rfl, AddChar.map_add_eq_mul, quarterChar_one, I_mul_I]

private theorem quarterChar_three : ZMod.stdAddChar (3 : ZMod 4) = -I := by
  rw [show (3 : ZMod 4) = 2 + 1 by rfl, AddChar.map_add_eq_mul,
    quarterChar_two, quarterChar_one, neg_one_mul]

private theorem quarterChar_difference (x : ZMod 4) :
    ZMod.stdAddChar x - ZMod.stdAddChar (-x) =
      2 * I * RHTower.quadraticCharacterFour x := by
  rw [AddChar.map_neg_eq_inv]
  fin_cases x
  · change ZMod.stdAddChar (0 : ZMod 4) - (ZMod.stdAddChar (0 : ZMod 4))⁻¹ =
      2 * I * RHTower.quadraticCharacterFour (0 : ZMod 4)
    rw [AddChar.map_zero_eq_one]
    norm_num [RHTower.quadraticCharacterFour, ZMod.χ₄]
  · change ZMod.stdAddChar (1 : ZMod 4) - (ZMod.stdAddChar (1 : ZMod 4))⁻¹ =
      2 * I * RHTower.quadraticCharacterFour (1 : ZMod 4)
    rw [quarterChar_one, map_one, inv_I]
    ring
  · change ZMod.stdAddChar (2 : ZMod 4) - (ZMod.stdAddChar (2 : ZMod 4))⁻¹ =
      2 * I * RHTower.quadraticCharacterFour (2 : ZMod 4)
    rw [quarterChar_two]
    norm_num [RHTower.quadraticCharacterFour, ZMod.χ₄]
  · change ZMod.stdAddChar (3 : ZMod 4) - (ZMod.stdAddChar (3 : ZMod 4))⁻¹ =
      2 * I * RHTower.quadraticCharacterFour (3 : ZMod 4)
    rw [quarterChar_three]
    norm_num [RHTower.quadraticCharacterFour, ZMod.χ₄, inv_I]
    ring

private theorem congruenceLFunction_sub {N : ℕ} [NeZero N]
    (f g : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun x => f x - g x) s = ZMod.LFunction f s - ZMod.LFunction g s := by
  simp only [ZMod.LFunction, sub_mul, Finset.sum_sub_distrib, mul_sub]

private theorem congruenceLFunction_mul {N : ℕ} [NeZero N]
    (c : ℂ) (f : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun x => c * f x) s = c * ZMod.LFunction f s := by
  simp only [ZMod.LFunction, mul_assoc, ← Finset.mul_sum]
  ring

/-- The quarter-phase sine zeta function is the conductor-four quadratic L-function. -/
theorem sinZeta_quarter_eq_beta (s : ℂ) :
    sinZeta (ZMod.toAddCircle (1 : ZMod 4)) s =
      DirichletCharacter.LFunction RHTower.quadraticCharacterFour s := by
  letI : Fact (1 < 4) := ⟨by omega⟩
  have h := congrArg (fun f : ZMod 4 → ℂ => ZMod.LFunction f s)
    (funext quarterChar_difference)
  rw [congruenceLFunction_sub, congruenceLFunction_mul] at h
  have hp := ZMod.LFunction_stdAddChar_eq_expZeta (1 : ZMod 4) s
    (Or.inl one_ne_zero)
  have hm := ZMod.LFunction_stdAddChar_eq_expZeta (-1 : ZMod 4) s
    (Or.inl (neg_ne_zero.mpr one_ne_zero))
  simp only [one_mul] at hp
  simp only [neg_one_mul, map_neg] at hm
  rw [hp, hm] at h
  rw [sinZeta_eq, h]
  change (2 * I * ZMod.LFunction RHTower.quadraticCharacterFour s) / (2 * I) =
    ZMod.LFunction RHTower.quadraticCharacterFour s
  field_simp

/-- The sine channel at every integer weight at least two is nonzero. -/
theorem sinZeta_quarter_nat_ne_zero (n : ℕ) :
    sinZeta (ZMod.toAddCircle (1 : ZMod 4)) ((n : ℂ) + 2) ≠ 0 := by
  rw [sinZeta_quarter_eq_beta]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _
    (Or.inl RHTower.quadraticCharacterFour_ne_one) (by
      have h : (1 : ℝ) ≤ (n : ℝ) + 2 := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      simpa using h)

private theorem toAddCircle_three :
    ZMod.toAddCircle (3 : ZMod 4) = -ZMod.toAddCircle (1 : ZMod 4) := by
  rw [show (3 : ZMod 4) = -1 by rfl, map_neg]

private theorem toAddCircle_two :
    ZMod.toAddCircle (2 : ZMod 4) = ZMod.toAddCircle (1 : ZMod 2) := by
  change ZMod.toAddCircle ((2 : ℤ) : ZMod 4) = ZMod.toAddCircle ((1 : ℤ) : ZMod 2)
  rw [ZMod.toAddCircle_intCast, ZMod.toAddCircle_intCast]
  norm_num

private theorem sum_zmod_four (f : ZMod 4 → ℂ) :
    ∑ x, f x = f 0 + f 1 + f 2 + f 3 := by
  calc
    _ = ∑ i : Fin 4, f (ZMod.finEquiv 4 i) :=
      (Fintype.sum_equiv (ZMod.finEquiv 4).toEquiv
        (fun i => f (ZMod.finEquiv 4 i)) f (fun _ => rfl)).symm
    _ = _ := Fin.sum_univ_four _

private theorem sum_zmod_two (f : ZMod 2 → ℂ) : ∑ x, f x = f 0 + f 1 := by
  calc
    _ = ∑ i : Fin 2, f (ZMod.finEquiv 2 i) :=
      (Fintype.sum_equiv (ZMod.finEquiv 2).toEquiv
        (fun i => f (ZMod.finEquiv 2 i)) f (fun _ => rfl)).symm
    _ = _ := Fin.sum_univ_two _

/-- The quarter-phase cosine channel is an explicit scalar multiple of Riemann zeta. -/
theorem cosZeta_quarter_nat_eq (n : ℕ) :
    cosZeta (ZMod.toAddCircle (1 : ZMod 4)) ((n : ℂ) + 2) =
      ((4 : ℂ) ^ (1 - ((n : ℂ) + 2)) - (2 : ℂ) ^ (1 - ((n : ℂ) + 2))) / 2 *
        riemannZeta ((n : ℂ) + 2) := by
  have hs : (n : ℂ) + 2 ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h4 := RHTower.sum_expZeta_eq 4 hs
  have h2 := RHTower.sum_expZeta_eq 2 hs
  rw [sum_zmod_four] at h4
  rw [sum_zmod_two] at h2
  simp only [map_zero, expZeta_zero, toAddCircle_three, toAddCircle_two] at h4 h2
  rw [cosZeta_eq]
  linear_combination h4 / 2 - h2 / 2

/-- The cosine channel is also nonzero at every integer weight at least two. -/
theorem cosZeta_quarter_nat_ne_zero (n : ℕ) :
    cosZeta (ZMod.toAddCircle (1 : ZMod 4)) ((n : ℂ) + 2) ≠ 0 := by
  rw [cosZeta_quarter_nat_eq]
  apply mul_ne_zero
  · apply div_ne_zero _ (by norm_num)
    have hpow : (4 : ℂ) ^ (1 - ((n : ℂ) + 2)) =
        (2 : ℂ) ^ (1 - ((n : ℂ) + 2)) * (2 : ℂ) ^ (1 - ((n : ℂ) + 2)) := by
      have h := Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := (2 : ℝ))
        (by norm_num) (by norm_num) (1 - ((n : ℂ) + 2) : ℂ)
      norm_num at h
      exact h
    rw [hpow, ← mul_sub_one]
    apply mul_ne_zero (by simp : (2 : ℂ) ^ (1 - ((n : ℂ) + 2)) ≠ 0)
    intro h
    have hn : ((n : ℂ) + 2).re ≠ 1 := by
      have hnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hlt : (1 : ℝ) < (n : ℝ) + 2 := by linarith
      simpa using ne_of_gt hlt
    exact RHTower.DQPT.dqpt_eta_factor_ne_zero hn (by linear_combination -h)
  · exact riemannZeta_ne_zero_of_one_le_re (by
      have h : (1 : ℝ) ≤ (n : ℝ) + 2 := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      simpa using h)

/-- Both analytic channels used by the quarter-period formula are nonzero in every weight. -/
theorem quarterPolylog_analytic_channels_nonzero (n : ℕ) :
    sinZeta (ZMod.toAddCircle (1 : ZMod 4)) ((n : ℂ) + 2) ≠ 0 ∧
      cosZeta (ZMod.toAddCircle (1 : ZMod 4)) ((n : ℂ) + 2) ≠ 0 :=
  ⟨sinZeta_quarter_nat_ne_zero n, cosZeta_quarter_nat_ne_zero n⟩


/-- The parity-selected analytic factor at `i`, before the nonzero normalization constants. -/
noncomputable def quarterPolylogAnalyticFactor (n : ℕ) : ℂ :=
  if Even (n + 2) then I * sinZeta (ZMod.toAddCircle (1 : ZMod 4)) ((n : ℂ) + 2)
  else cosZeta (ZMod.toAddCircle (1 : ZMod 4)) ((n : ℂ) + 2)

/-- The parity selection in the single-valued polylogarithm formula never annihilates this factor. -/
theorem quarterPolylogAnalyticFactor_ne_zero (n : ℕ) :
    quarterPolylogAnalyticFactor n ≠ 0 := by
  unfold quarterPolylogAnalyticFactor
  split_ifs
  · exact mul_ne_zero I_ne_zero (sinZeta_quarter_nat_ne_zero n)
  · exact cosZeta_quarter_nat_ne_zero n

end GaloisForLFunctions.HTGeometry
#print axioms GaloisForLFunctions.HTGeometry.quarterPolylogAnalyticFactor_ne_zero

#print axioms GaloisForLFunctions.HTGeometry.quarterPolylog_analytic_channels_nonzero
