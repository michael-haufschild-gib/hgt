import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicIntegralReduction
import Mathlib.Tactic.Group

/-! A residue unipotent supported across two disjoint blocks has an
integral lift with the same support. A diagonal torus with strictly
larger exponents on its target block contracts the lift into the
first principal congruence subgroup. -/

noncomputable section

open Matrix

namespace GlobalTheory.GLp

variable {p : ℕ} [Fact p.Prime] {n : Type*} [Fintype n] [DecidableEq n]

private theorem prime_ne_zero : (p : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- The diagonal matrix of integer powers of the rational uniformizer. -/
def uniformizerTorus (a : n → ℤ) : GL n ℚ_[p] :=
  ⟨Matrix.diagonal (fun i => (p : ℚ_[p]) ^ a i),
    Matrix.diagonal (fun i => ((p : ℚ_[p]) ^ a i)⁻¹),
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (zpow_ne_zero _ prime_ne_zero),
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (zpow_ne_zero _ prime_ne_zero)⟩

theorem uniformizerTorus_conj_sub_apply (a : n → ℤ) (x : GL n ℚ_[p]) (i j : n) :
    ((uniformizerTorus (p := p) a * x * (uniformizerTorus a)⁻¹).val - 1) i j =
      (p : ℚ_[p]) ^ a i * (x.val - 1) i j * ((p : ℚ_[p]) ^ a j)⁻¹ := by
  let t := uniformizerTorus (p := p) a
  have e : (t * x * t⁻¹).val - 1 = t.val * (x.val - 1) * (t⁻¹).val := by
    have h : t.val * (t⁻¹).val = 1 := t.mul_inv
    simp only [mul_sub, sub_mul, mul_one, Units.val_mul, h]
  rw [e]
  change (Matrix.diagonal (fun i => (p : ℚ_[p]) ^ a i) * (x.val - 1) *
    Matrix.diagonal (fun i => ((p : ℚ_[p]) ^ a i)⁻¹)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem square_zero_of_block_support {R : Type*} [Ring R]
    (s : n → Prop) (B : Matrix n n R) (hB : ∀ i j, ¬ (s i ∧ ¬ s j) → B i j = 0) :
    B * B = 0 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : s k
  · rw [hB i k (fun h => h.2 hk), zero_mul]
  · rw [hB k j (fun h => hk h.1), mul_zero]

theorem exists_integral_radical_lift_of_block_support (s : n → Prop)
    (u : GL n (ZMod p)) (hu : ∀ i j, ¬ (s i ∧ ¬ s j) → (u.val - 1) i j = 0) :
    ∃ b : GL n ℤ_[p], integralReduction p n b = u ∧
      ∀ i j, ¬ (s i ∧ ¬ s j) → (b.val - 1) i j = 0 := by
  classical
  choose entries he using fun i j : n =>
    ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) ((u.val - 1) i j)
  let B : Matrix n n ℤ_[p] := fun i j => if s i ∧ ¬ s j then entries i j else 0
  have hB (i j : n) (h : ¬ (s i ∧ ¬ s j)) : B i j = 0 := if_neg h
  have hB0 : B * B = 0 := square_zero_of_block_support s B hB
  let b : GL n ℤ_[p] := ⟨1 + B, 1 - B,
    by simp [add_mul, mul_sub, hB0],
    by simp [sub_mul, mul_add, hB0]⟩
  have hredB : PadicInt.toZMod.mapMatrix B = u.val - 1 := by
    ext i j
    change PadicInt.toZMod (B i j) = _
    by_cases hs : s i ∧ ¬ s j
    · rw [show B i j = entries i j from if_pos hs, he]
    · rw [hB i j hs, hu i j hs, map_zero]
  refine ⟨b, Units.ext ?_, ?_⟩
  · change PadicInt.toZMod.mapMatrix (1 + B) = u.val
    rw [map_add, map_one, hredB]
    abel
  · intro i j hij
    change (1 + B - 1) i j = 0
    rw [add_sub_cancel_left]
    exact hB i j hij

theorem exists_integral_radical_lift_contracted (s : n → Prop) (a : n → ℤ)
    (ha : ∀ i j, s i → ¬ s j → a j < a i)
    (u : GL n (ZMod p)) (hu : ∀ i j, ¬ (s i ∧ ¬ s j) → (u.val - 1) i j = 0) :
    ∃ b : GL n ℤ_[p], integralReduction p n b = u ∧
      uniformizerTorus (p := p) a * integralInclusion p n b * (uniformizerTorus a)⁻¹ ∈
        principalCongruenceOne p n := by
  obtain ⟨b, hb, hB⟩ := exists_integral_radical_lift_of_block_support s u hu
  refine ⟨b, hb, ?_⟩
  apply (mem_principalCongruenceOne_iff p n _).mpr
  intro i j
  rw [uniformizerTorus_conj_sub_apply]
  have hentry : (((integralInclusion p n b).val - 1) i j : ℚ_[p]) =
      (((b.val - 1) i j : ℤ_[p]) : ℚ_[p]) := by
    change (((algebraMap ℤ_[p] ℚ_[p]).mapMatrix b.val - 1) i j : ℚ_[p]) = _
    rw [← map_one (algebraMap ℤ_[p] ℚ_[p]).mapMatrix, ← map_sub]
    rfl
  rw [hentry]
  by_cases hs : s i ∧ ¬ s j
  · have hpow : ‖(p : ℚ_[p]) ^ (a i - a j)‖ < 1 := by
      have hpos : 0 < a i - a j := sub_pos.mpr (ha i j hs.1 hs.2)
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hpos.le
      rw [hm, zpow_natCast, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) Padic.norm_p_lt_one (by omega)
    rw [show (p : ℚ_[p]) ^ a i * ((b.val - 1) i j : ℤ_[p]) * ((p : ℚ_[p]) ^ a j)⁻¹ =
        (p : ℚ_[p]) ^ (a i - a j) * ((b.val - 1) i j : ℤ_[p]) by
      rw [zpow_sub₀ prime_ne_zero, div_eq_mul_inv]
      ac_rfl, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) ((b.val - 1) i j).2).trans_lt hpow
  · rw [hB i j hs, PadicInt.coe_zero, mul_zero, zero_mul, norm_zero]
    exact zero_lt_one

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.exists_integral_radical_lift_of_block_support
#print axioms GlobalTheory.GLp.exists_integral_radical_lift_contracted
