import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerExtensionJacobiSums
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerPuncturedJacobiCount

/-!
# Exact punctured-chart counts over every finite extension

Character orthogonality expands the literal radical fibers into Jacobi
sums. The trivial character contributes the punctured line count;
the remaining characters contribute either `-1` or a common signed
middle-field size. Their gcd counts identify the latter multiplicity
with twice the actual global regular differential dimension.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "N" => p ^ (s + 1) + 1
local notation "m" => p ^ (d + 1) - 1
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "c" => (kummerTraceConstant p s)⁻¹ ^ R
local notation "g" => Module.finrank K
  (globalRegularDifferentials K (SquareKummerField p s c (p ^ (d + 1) - 2) R))
variable (E : Type*) [Field E] [Fintype E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
local notation "H" => unitEndomorphismCharacters («R» := ℂ) (powMonoidHom M : Eˣ →* Eˣ)
local instance : Fintype (MulChar E ℂ) := Fintype.ofFinite _

/-- The literal punctured three-point chart has the exact extension-field count, including branch exponent zero. -/
theorem primePowerKummer_punctured_extension_count :
    (∑ x ∈ Finset.univ.filter (fun x : E => x ≠ 0 ∧ x ≠ 1),
      (Nat.card {z : E | z ^ M = (primePowerKummerExtensionCoefficient p d n r E : E) *
        x * (1 - x) ^ (m * R)} : ℂ)) =
      (Fintype.card E : ℂ) - 1 - (m * Nat.gcd N R : ℕ) +
        (-1 : ℂ) ^ (Module.finrank K E + 1) *
          (p : ℂ) ^ ((s + 1) * Module.finrank K E) * (2 * g : ℕ) := by
  let U := (-1 : ℂ) ^ (Module.finrank K E + 1) *
    (p : ℂ) ^ ((s + 1) * Module.finrank K E)
  let f : H → ℂ := fun χ =>
    χ.val (primePowerKummerExtensionCoefficient p d n r E : E) *
      jacobiSum χ.val (χ.val ^ (m * R))
  have hpoint (χ : H) : f χ =
      (if χ = 1 then (Fintype.card E : ℂ) - 1 else 0) +
        (if χ.val ^ (m * R) = 1 then -1 else U) := by
    by_cases hχ : χ = 1
    · subst χ
      have hone : ((1 : H) : MulChar E ℂ) = 1 := rfl
      change (1 : MulChar E ℂ) (primePowerKummerExtensionCoefficient p d n r E : E) *
        jacobiSum (1 : MulChar E ℂ) ((1 : MulChar E ℂ) ^ (m * R)) = _
      simp only [hone, one_pow, MulChar.one_apply_coe, jacobiSum_one_one, one_mul, ite_true]
      ring
    · rw [if_neg hχ, zero_add]
      exact primePowerKummer_extension_weighted_jacobi p d n r E χ
        (fun h => hχ (Subtype.ext h))
  have hfirst : (∑ χ : H, if χ = 1 then (Fintype.card E : ℂ) - 1 else 0) =
      (Fintype.card E : ℂ) - 1 := by
    rw [Finset.sum_eq_single (1 : H)]
    · rw [if_pos rfl]
    · intro χ _ hχ
      rw [if_neg hχ]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hkernel : (Finset.univ.filter (fun χ : H => χ.val ^ (m * R) = 1)).card =
      m * Nat.gcd N R := by
    rw [← Fintype.card_subtype (fun χ : H => χ.val ^ (m * R) = 1),
      ← Nat.card_eq_fintype_card]
    exact primePowerKummer_trivial_gauss_character_card p d n r E
  have hactive : (Finset.univ.filter (fun χ : H => χ.val ^ (m * R) ≠ 1)).card = 2 * g := by
    rw [← Fintype.card_subtype (fun χ : H => χ.val ^ (m * R) ≠ 1),
      ← Nat.card_eq_fintype_card]
    exact primePowerKummer_active_gauss_character_card_eq_twice_genus p d n r E c
  have hsum : (∑ χ : H, f χ) =
      (Fintype.card E : ℂ) - 1 - (m * Nat.gcd N R : ℕ) + U * (2 * g : ℕ) := by
    calc
      _ = ∑ χ : H, ((if χ = 1 then (Fintype.card E : ℂ) - 1 else 0) +
          (if χ.val ^ (m * R) = 1 then -1 else U)) :=
        Finset.sum_congr rfl (fun χ _ => hpoint χ)
      _ = _ := by
        rw [Finset.sum_add_distrib, hfirst, Finset.sum_ite,
          Finset.sum_const, Finset.sum_const, hkernel, hactive]
        simp only [nsmul_eq_mul]
        ring
  have hcount := finiteField_punctured_kummer_fiber_sum («K» := E) (M - 1) (m * R)
    (primePowerKummerExtensionCoefficient p d n r E)
  rw [Nat.sub_add_cancel (primePowerKummerCyclicDegree_pos p d n)] at hcount
  exact hcount.trans hsum

/-- The cardinality of the actual punctured point set has the intrinsic-genus extension formula. -/
theorem primePowerKummer_punctured_extension_points_card :
    (Nat.card (PuncturedKummerPoints (M - 1) (m * R)
      (primePowerKummerExtensionCoefficient p d n r E)) : ℂ) =
      (Fintype.card E : ℂ) - 1 - (m * Nat.gcd N R : ℕ) +
        (-1 : ℂ) ^ (Module.finrank K E + 1) *
          (p : ℂ) ^ ((s + 1) * Module.finrank K E) * (2 * g : ℕ) := by
  rw [puncturedKummerPoints_card, Nat.cast_sum,
    Nat.sub_add_cancel (primePowerKummerCyclicDegree_pos p d n)]
  exact primePowerKummer_punctured_extension_count p d n r E

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
