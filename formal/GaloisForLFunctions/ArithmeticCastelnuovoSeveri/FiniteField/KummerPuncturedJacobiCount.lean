import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerCharacterFibers
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.PuncturedJacobiSums

/-!
# Jacobi sums for punctured Kummer point counts

On the chart omitting zero and one, every defining value is nonzero.
Character orthogonality counts each radical fiber, and interchanging
the finite sums turns the complete chart count into Jacobi sums.
The formula includes branch exponent zero without a separate case.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable {K : Type*} [Field K] [Fintype K]

local instance : Fintype (MulChar K ℂ) := Fintype.ofFinite _

/-- Literal points of the three-point Kummer equation away from the coordinates zero and one. -/
abbrev PuncturedKummerPoints (n a : ℕ) (c : Kˣ) :=
  (x : {x : K // x ≠ 0 ∧ x ≠ 1}) × {z : K // z ^ (n + 1) = (c : K) * x.val * (1 - x.val) ^ a}

/-- The cardinality of the literal punctured point set is the sum of its radical-fiber cardinalities. -/
theorem puncturedKummerPoints_card (n a : ℕ) (c : Kˣ) :
    Nat.card (PuncturedKummerPoints n a c) =
      ∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0 ∧ x ≠ 1),
        Nat.card {z : K | z ^ (n + 1) = (c : K) * x * (1 - x) ^ a} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Nat.card_eq_fintype_card]
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    exact ⟨⟨x, (Finset.mem_filter.mp hx).2⟩, Finset.mem_univ _, rfl⟩
  · intro x _
    rfl

/-- The sum of actual radical-fiber cardinalities on the punctured chart is the full Jacobi character sum. -/
theorem finiteField_punctured_kummer_fiber_sum (n a : ℕ) (c : Kˣ) :
    (∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0 ∧ x ≠ 1),
      (Nat.card {z : K | z ^ (n + 1) = (c : K) * x * (1 - x) ^ a} : ℂ)) =
      ∑ χ : unitEndomorphismCharacters (R := ℂ) (powMonoidHom (n + 1) : Kˣ →* Kˣ),
        χ.val (c : K) * jacobiSum χ.val (χ.val ^ a) := by
  let S := Finset.univ.filter (fun x : K => x ≠ 0 ∧ x ≠ 1)
  let H := unitEndomorphismCharacters (R := ℂ) (powMonoidHom (n + 1) : Kˣ →* Kˣ)
  change (∑ x ∈ S, (Nat.card {z : K | z ^ (n + 1) = (c : K) * x * (1 - x) ^ a} : ℂ)) =
    ∑ χ : H, χ.val (c : K) * jacobiSum χ.val (χ.val ^ a)
  calc
    _ = ∑ x ∈ S, ∑ χ : H, χ.val ((c : K) * x * (1 - x) ^ a) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      exact finiteField_nonzero_power_fiber_character_sum n _
        (mul_ne_zero (mul_ne_zero c.ne_zero hx'.1)
          (pow_ne_zero a (sub_ne_zero.mpr (Ne.symm hx'.2))))
    _ = ∑ χ : H, ∑ x ∈ S, χ.val ((c : K) * x * (1 - x) ^ a) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      exact finiteField_punctured_monomial_character_sum χ.val (c : K) a

/-- The actual finite punctured point set is counted by its Jacobi character expansion. -/
theorem puncturedKummerPoints_card_eq_jacobi_sum (n a : ℕ) (c : Kˣ) :
    (Nat.card (PuncturedKummerPoints n a c) : ℂ) =
      ∑ χ : unitEndomorphismCharacters (R := ℂ) (powMonoidHom (n + 1) : Kˣ →* Kˣ),
        χ.val (c : K) * jacobiSum χ.val (χ.val ^ a) := by
  rw [puncturedKummerPoints_card, Nat.cast_sum]
  exact finiteField_punctured_kummer_fiber_sum n a c

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
