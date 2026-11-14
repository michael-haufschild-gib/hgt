import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerTraceConstants
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Rational fibers of the finite-field norm equation

Over the field with `Q²` elements, `z^(Q+1)=a` has a solution exactly when
`a^Q=a`. Every nonzero soluble fiber has `Q+1` elements. The proof identifies
the image and kernel of complementary power maps in a finite cyclic group.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open scoped Classical

/-- Complementary power maps in a finite cyclic group form an exact pair. -/
theorem cyclic_power_range_eq_ker (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]
    {d e : ℕ} (hd : 0 < d) (hcard : Nat.card G = d * e) :
    (powMonoidHom d : G →* G).range = (powMonoidHom e : G →* G).ker := by
  have hc : Nat.card (powMonoidHom d : G →* G).range =
      Nat.card (powMonoidHom e : G →* G).ker := by
    rw [IsCyclic.card_powMonoidHom_range, IsCyclic.card_powMonoidHom_ker,
      Nat.gcd_eq_right (show d ∣ Nat.card G from ⟨e, hcard⟩),
      Nat.gcd_eq_right (show e ∣ Nat.card G from ⟨d, hcard.trans (Nat.mul_comm _ _)⟩),
      hcard, Nat.mul_div_right e hd]
  apply Subgroup.eq_of_le_of_card_ge ?_ hc.ge
  rintro x ⟨y, rfl⟩
  change (y ^ d) ^ e = 1
  rw [← pow_mul, ← hcard]
  exact pow_card_eq_one'

variable (p : ℕ) [Fact p.Prime]

/-- The order of the unit group factors into the norm degree and fixed-field unit count. -/
theorem squareConstantField_units_card (s : ℕ) :
    Nat.card (SquareConstantField p s)ˣ = (p ^ (s + 1) + 1) * (p ^ (s + 1) - 1) := by
  rw [Nat.card_units, squareConstantField_card, Nat.mul_comm 2 (s + 1), pow_mul, pow_two]
  have hsub := Nat.sub_add_cancel
    (Nat.one_le_pow (s + 1) p (Fact.out : p.Prime).pos)
  have he : (p ^ (s + 1) + 1) * (p ^ (s + 1) - 1) + 1 =
      p ^ (s + 1) * p ^ (s + 1) := by nlinarith only [hsub]
  omega

/-- A unit is a norm exactly when it is killed by the complementary power map. -/
theorem squareConstantField_unit_norm_iff (s : ℕ) (a : (SquareConstantField p s)ˣ) :
    (∃ z : (SquareConstantField p s)ˣ, z ^ (p ^ (s + 1) + 1) = a) ↔
      a ^ (p ^ (s + 1) - 1) = 1 := by
  have h := cyclic_power_range_eq_ker (SquareConstantField p s)ˣ
    (Nat.succ_pos (p ^ (s + 1))) (squareConstantField_units_card p s)
  simpa only [MonoidHom.mem_range, MonoidHom.mem_ker, powMonoidHom_apply] using
    (congrArg (a ∈ ·) h).to_iff

/-- The norm lands in the fixed field of the `Q`-power Frobenius. -/
theorem squareConstantField_norm_fixed (s : ℕ) (z : SquareConstantField p s) :
    (z ^ (p ^ (s + 1) + 1)) ^ p ^ (s + 1) = z ^ (p ^ (s + 1) + 1) := by
  rw [pow_succ, mul_pow, squareConstantField_frobenius_sq, mul_comm]

/-- The norm equation is soluble precisely on the Frobenius-fixed elements. -/
theorem squareConstantField_exists_norm_iff (s : ℕ) (a : SquareConstantField p s) :
    (∃ z : SquareConstantField p s, z ^ (p ^ (s + 1) + 1) = a) ↔
      a ^ p ^ (s + 1) = a := by
  constructor
  · rintro ⟨z, rfl⟩
    exact squareConstantField_norm_fixed p s z
  · intro ha
    by_cases ha0 : a = 0
    · exact ⟨0, by simp only [ha0, zero_pow (Nat.succ_ne_zero _)]⟩
    let u : (SquareConstantField p s)ˣ := Units.mk0 a ha0
    have hu : u ^ (p ^ (s + 1) - 1) = 1 := by
      apply Units.ext
      change a ^ (p ^ (s + 1) - 1) = 1
      apply mul_right_cancel₀ ha0
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel
        (Nat.one_le_pow (s + 1) p (Fact.out : p.Prime).pos)]
      exact ha
    obtain ⟨z, hz⟩ := (squareConstantField_unit_norm_iff p s u).mpr hu
    exact ⟨z, congrArg Units.val hz⟩

/-- Every nonempty unit norm fiber has exactly `Q+1` elements. -/
theorem squareConstantField_unit_norm_fiber_card (s : ℕ)
    (a : (SquareConstantField p s)ˣ) :
    Nat.card {z : (SquareConstantField p s)ˣ |
      z ^ (p ^ (s + 1) + 1) = a ^ (p ^ (s + 1) + 1)} = p ^ (s + 1) + 1 := by
  have he := (powMonoidHom (p ^ (s + 1) + 1) :
    (SquareConstantField p s)ˣ →* (SquareConstantField p s)ˣ).fiberEquivKer a
  have hc := Nat.card_congr he
  simp only [Set.preimage, Set.mem_singleton_iff, powMonoidHom_apply] at hc
  rw [hc, IsCyclic.card_powMonoidHom_ker,
    Nat.gcd_eq_right (by rw [Nat.card_units]; exact squareConstantField_degree_dvd p s)]

/-- A nonzero power fiber consists entirely of units. -/
def nonzeroPowerFiberEquivUnits {K : Type*} [Field K] (n : ℕ) (a : K) (ha : a ≠ 0) :
    {z : K | z ^ (n + 1) = a} ≃ {z : Kˣ | z ^ (n + 1) = Units.mk0 a ha} where
  toFun z := ⟨Units.mk0 z.val (by
    intro hz
    exact ha (z.property.symm.trans (by rw [hz, zero_pow (Nat.succ_ne_zero _)]))),
    Units.ext z.property⟩
  invFun z := ⟨z.val, congrArg Units.val z.property⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Units.ext rfl)

/-- Every nonzero Frobenius-fixed value has exactly `Q+1` norm preimages. -/
theorem squareConstantField_norm_fiber_card_of_fixed (s : ℕ)
    (a : SquareConstantField p s) (ha : a ≠ 0) (hfixed : a ^ p ^ (s + 1) = a) :
    Nat.card {z : SquareConstantField p s | z ^ (p ^ (s + 1) + 1) = a} =
      p ^ (s + 1) + 1 := by
  obtain ⟨z, hz⟩ := (squareConstantField_exists_norm_iff p s a).mpr hfixed
  have hz0 : z ≠ 0 := by
    intro h
    exact ha (hz.symm.trans (by rw [h, zero_pow (Nat.succ_ne_zero _)]))
  have hu : (Units.mk0 z hz0) ^ (p ^ (s + 1) + 1) = Units.mk0 a ha := Units.ext hz
  rw [Nat.card_congr (nonzeroPowerFiberEquivUnits (p ^ (s + 1)) a ha), ← hu]
  exact squareConstantField_unit_norm_fiber_card p s (Units.mk0 z hz0)

/-- The complete fiber count, including zero and nonsoluble values. -/
theorem squareConstantField_norm_fiber_card (s : ℕ) (a : SquareConstantField p s) :
    Nat.card {z : SquareConstantField p s | z ^ (p ^ (s + 1) + 1) = a} =
      if a = 0 then 1 else if a ^ p ^ (s + 1) = a then p ^ (s + 1) + 1 else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    rw [if_pos rfl]
    letI : Nonempty {z : SquareConstantField p s | z ^ (p ^ (s + 1) + 1) = 0} :=
      ⟨⟨0, zero_pow (Nat.succ_ne_zero _)⟩⟩
    letI : Subsingleton {z : SquareConstantField p s | z ^ (p ^ (s + 1) + 1) = 0} :=
      ⟨fun x y => Subtype.ext (((pow_eq_zero_iff (Nat.succ_ne_zero _)).mp x.property).trans
        ((pow_eq_zero_iff (Nat.succ_ne_zero _)).mp y.property).symm)⟩
    exact Nat.card_unique
  · rw [if_neg ha]
    by_cases hf : a ^ p ^ (s + 1) = a
    · rw [if_pos hf]
      exact squareConstantField_norm_fiber_card_of_fixed p s a ha hf
    · rw [if_neg hf]
      exact Nat.card_eq_zero.mpr (Or.inl ⟨fun z =>
        hf ((squareConstantField_exists_norm_iff p s a).mp ⟨z.val, z.property⟩)⟩)

/-- Each affine fiber of the literal Kummer equation has an exact finite-field count. -/
theorem squareKummer_affine_fiber_card (s : ℕ) (c : (SquareConstantField p s)ˣ)
    (b R : ℕ) (y : SquareConstantField p s) :
    Nat.card {z : SquareConstantField p s |
      z ^ (p ^ (s + 1) + 1) = (c : SquareConstantField p s) * y * (1 - y ^ (b + 1)) ^ R} =
    if (kummerBranch c b R).eval y = 0 then 1
    else if ((kummerBranch c b R).eval y) ^ p ^ (s + 1) = (kummerBranch c b R).eval y
    then p ^ (s + 1) + 1 else 0 := by
  simpa only [kummerBranch, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one] using
    squareConstantField_norm_fiber_card p s ((kummerBranch c b R).eval y)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
