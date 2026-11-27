import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraCuspidalRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicBlockMatrices

/-! Conjugation of a leading block reindexes its Levi fibre. Consequently
the Whittaker derivative of a class function is a class function. -/

noncomputable section
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]

theorem res_conj_left (χ : Gn g (a + b) → ℂ) (hχ : IsClass χ)
    (x y : Gn g a) (z : Gn g b) :
    res a b χ (y * x * y⁻¹) z = res a b χ x z := by
  let P := twoBlockParabolic g a b
  let p : P := ⟨upperBlockUnit y 0 1, inPar_upperBlockMatrix y.val 0 1⟩
  have hp : twoBlockLevi p = (y, 1) := twoBlockLevi_upperBlockUnit y 0 1
  let e : P ≃ P := (MulAut.conj p).toEquiv
  have he (u : P) : e u = p * u * p⁻¹ := by simp [e]
  have hπ (u : P) : twoBlockLevi (e u) =
      (y * (twoBlockLevi u).1 * y⁻¹, (twoBlockLevi u).2) := by
    rw [he, map_mul, map_mul, map_inv, hp]
    apply Prod.ext
    · rfl
    · change 1 * (twoBlockLevi u).2 * (1 : Gn g b)⁻¹ = _
      simp
  rw [res_eq_sum_diagonal_fibre, res_eq_sum_diagonal_fibre]
  congr 1
  symm
  refine Fintype.sum_equiv e _ _ fun u => ?_
  have hχe : χ (e u).val = χ u.val := by
    rw [he]
    exact hχ u.val p.val
  rw [hχe, hπ]
  refine if_congr ?_ rfl rfl
  simp only [Prod.ext_iff, mul_right_cancel_iff, mul_left_cancel_iff]

/-- The Whittaker derivative is invariant under conjugacy in its remaining block. -/
theorem der_isClass (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (ha : a ≤ n)
    (χ : Gn g n → ℂ) (hχ : IsClass χ) : IsClass (der ψ a χ) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  intro x y
  change wh ψ (res a (a + b - a) χ (y * x * y⁻¹)) = wh ψ (res a (a + b - a) χ x)
  rw [Nat.add_sub_cancel_left]
  exact congrArg (wh ψ) (funext fun z => res_conj_left χ hχ x y z)

end GlobalTheory.GLq
