import GaloisForLFunctions.HTGeometry.CosineReflectionCoincidence
import Mathlib.Algebra.Polynomial.Roots

/-!
# Infinitely many nonreal diagonal points of the cosine curve

The curve `w ↦ (source w, source (-w))` meets the diagonal at infinitely many
nonreal parameters with pairwise distinct diagonal coordinates. The argument
uses exact square identities and the deck transformations of cosine.
-/

namespace GaloisForLFunctions.HTGeometry.CosineInfiniteDiagonal

open Complex LabeledCosineDescent CosineReflectionCoincidence

noncomputable section

def radius (n : ℕ) : ℝ := Real.sqrt (81 * (n + 1 : ℝ) ^ 2 - 1)

def point (n : ℕ) : ℂ := 3 / 2 * I * (n + 1 : ℂ) * (radius n : ℂ)

def lift (n : ℕ) : ℂ := Real.pi * (n + 1 : ℂ) + I * Real.pi * (radius n : ℂ) / 9

theorem radius_sq (n : ℕ) : radius n ^ 2 = 81 * (n + 1 : ℝ) ^ 2 - 1 := by
  apply Real.sq_sqrt
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem radius_ne_zero (n : ℕ) : radius n ≠ 0 := by
  intro h
  have hs := radius_sq n
  rw [h] at hs
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem point_im (n : ℕ) : (point n).im = 3 / 2 * (n + 1 : ℝ) * radius n := by
  simp [point, mul_assoc]

theorem point_nonreal (n : ℕ) : (point n).im ≠ 0 := by
  rw [point_im]
  apply mul_ne_zero
  · apply mul_ne_zero (by norm_num)
    exact_mod_cast Nat.succ_ne_zero n
  · exact radius_ne_zero n

theorem point_coincidence (n : ℕ) : source (point n) = source (-point n) := by
  have hs : (radius n : ℂ) ^ 2 = 81 * (n + 1 : ℂ) ^ 2 - 1 := by
    exact_mod_cast radius_sq n
  apply (coincidence_iff _).mpr
  refine ⟨(n : ℤ) + 1, ?_⟩
  push_cast
  simp only [point, mul_pow, hs, I_sq]
  ring

theorem source_point (n : ℕ) : source (point n) = Complex.cos (lift n) := by
  apply descendedCos_of_square
  have hs : (radius n : ℂ) ^ 2 = 81 * (n + 1 : ℂ) ^ 2 - 1 := by
    exact_mod_cast radius_sq n
  dsimp [lift, point]
  linear_combination -(Real.pi : ℂ) ^ 2 / 81 * hs +
    (Real.pi : ℂ) ^ 2 * (radius n : ℂ) ^ 2 / 81 * Complex.I_sq

theorem lift_im (n : ℕ) : (lift n).im = Real.pi * radius n / 9 := by
  simp [lift]

theorem source_point_injective : Function.Injective (fun n => source (point n)) := by
  intro n m h
  dsimp only at h
  rw [source_point, source_point] at h
  obtain ⟨k, hk | hk⟩ := Complex.cos_eq_cos_iff.mp h
  all_goals
    have hi := congrArg Complex.im hk
    simp [lift_im] at hi
  · have hr : radius m = radius n := by
      exact hi
    have hs := radius_sq m
    rw [hr, radius_sq] at hs
    have he : (n : ℝ) = m := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
    exact_mod_cast he
  · have hr : radius m = -radius n := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      linear_combination 9 * hi
    have hs := radius_sq m
    rw [hr, neg_sq, radius_sq] at hs
    have he : (n : ℝ) = m := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
    exact_mod_cast he

theorem point_injective : Function.Injective point := by
  intro n m h
  exact source_point_injective (congrArg source h)

theorem infinite_coincidences_avoiding (p : Polynomial ℂ) (hp : p ≠ 0) :
    Set.Infinite {w : ℂ | w.im ≠ 0 ∧ source w = source (-w) ∧ p.eval (source w) ≠ 0} := by
  let bad : Set ℕ := {n | p.eval (source (point n)) = 0}
  have hb : bad.Finite :=
    (Polynomial.finite_setOf_isRoot hp).preimage source_point_injective.injOn
  have hi : (Set.univ \ bad).Infinite := Set.infinite_univ.sdiff hb
  apply (hi.image point_injective.injOn).mono
  rintro w ⟨n, hn, rfl⟩
  exact ⟨point_nonreal n, point_coincidence n, hn.2⟩

end

end GaloisForLFunctions.HTGeometry.CosineInfiniteDiagonal
