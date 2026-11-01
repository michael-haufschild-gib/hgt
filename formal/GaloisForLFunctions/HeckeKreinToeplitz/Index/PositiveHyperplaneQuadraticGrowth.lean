import GaloisForLFunctions.HTGeometry.BoundedSecondDifferences
import GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling.PolarSecondDifference
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexUnderRotationDampingAndCoalescence

/-!
# Quadratic growth on a positive unitary-character hyperplane

A unitary twist converts the character constraint to total mass zero.
On each integer tower the polar-index identity makes the second difference
positive definite, hence bounded. Two discrete integrations give quadratic
growth of the original kernel.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AdelicKreinGeometry
open GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- A positive-definite second difference forces quadratic growth on an integer tower. -/
theorem quadratic_bound_of_posDef_secondDiff (q : Multiplicative ℤ → ℂ)
    (hq : IsPosDefKernel (secondDiff q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖q (Multiplicative.ofAdd (n : ℤ))‖ ≤ C * ((n : ℝ) + 1) ^ 2 := by
  let f : ℕ → ℂ := fun n => q (Multiplicative.ofAdd (n : ℤ))
  have hM : 0 ≤ (secondDiff q 1).re := (norm_nonneg _).trans (hq.norm_le 1)
  apply exists_quadratic_bound_of_second_difference f hM
  intro n
  have hplus : Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ) * Multiplicative.ofAdd (1 : ℤ) =
      Multiplicative.ofAdd ((n + 2 : ℕ) : ℤ) := by
    change Multiplicative.ofAdd (((n + 1 : ℕ) : ℤ) + 1) = _
    congr 1
  have hminus : Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ) * Multiplicative.ofAdd (-1 : ℤ) =
      Multiplicative.ofAdd (n : ℤ) := by
    change Multiplicative.ofAdd (((n + 1 : ℕ) : ℤ) + -1) = _
    congr 1
    push_cast
    ring
  have he : f (n + 2) - f (n + 1) - (f (n + 1) - f n) =
      -secondDiff q (Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ)) := by
    rw [secondDiff, hplus, hminus]
    dsimp only [f]
    ring
  rw [he, norm_neg]
  exact hq.norm_le _

variable {G : Type*} [Group G] {k : G → ℂ}

/-- The conjugate unitary twist turns character-mass positivity into total-mass positivity. -/
theorem nonneg_conjChar_twist_of_mass_zero (χ : G →* ℂ) (hχ : IsUnitaryChar χ)
    (hpos : ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      charEval χ x c = 0 → 0 ≤ hermQuad (gram k x) c)
    (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ) (hc : ∑ i, c i = 0) :
    0 ≤ hermQuad (gram (fun g => conjChar χ g * k g) x) c := by
  rw [hermQuad_gram_twist (isUnitaryChar_conjChar hχ)]
  apply hpos
  rw [charEval_apply]
  calc
    ∑ i, (conjChar χ (x i) * c i) * χ (x i) =
        ∑ i, c i * (conjChar χ (x i) * χ (x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, c i := by simp only [conjChar_mul_self hχ, mul_one]
    _ = 0 := hc

/-- A positive unitary-character mass hyperplane forces quadratic growth on every cyclic
subgroup, even when the ambient group is nonabelian. -/
theorem cyclic_quadratic_of_positive_unitary_hyperplane
    (hk : IsHermKernel k) (χ : G →* ℂ) (hχ : IsUnitaryChar χ)
    (hpos : ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      charEval χ x c = 0 → 0 ≤ hermQuad (gram k x) c) (g : G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖k (g ^ n)‖ ≤ C * ((n : ℝ) + 1) ^ 2 := by
  let l : G → ℂ := fun h => conjChar χ h * k h
  have hl : IsHermKernel l := by
    intro h
    change conjChar χ h⁻¹ * k h⁻¹ = conj (conjChar χ h * k h)
    rw [map_inv_eq_inv, inv_eq_conj_of_unitary (isUnitaryChar_conjChar hχ), hk, map_mul]
  let f : Multiplicative ℤ →* G := zpowersHom G g
  let q : Multiplicative ℤ → ℂ := l ∘ f
  have hq : IsHermKernel q := hl.comp f
  have hqp (n : ℕ) (x : Fin n → Multiplicative ℤ) (c : Fin n → ℂ)
      (hc : ∑ i, c i = 0) : 0 ≤ hermQuad (gram q x) c := by
    have he : gram q x = gram l (f ∘ x) := by
      ext i j
      simp only [gram, q, Function.comp_apply, map_mul, map_inv]
    rw [he]
    exact nonneg_conjChar_twist_of_mass_zero χ hχ hpos n (f ∘ x) c hc
  have hpolar : polarIndex q = 0 := by
    apply le_antisymm ?_ bot_le
    refine iSup₂_le fun n x => ?_
    have he : negIndexOn (gram q x) (LinearMap.ker (totalMass (Fin n))) = 0 :=
      negIndexOn_eq_zero_of_nonneg fun c hc => hqp n x c (LinearMap.mem_ker.mp hc)
    rw [he, Nat.cast_zero]
    exact zero_le
  have hsecond : IsPosDefKernel (secondDiff q) := by
    apply (isPosDefKernel_iff (isHermKernel_secondDiff hq)).mpr
    rw [← polarIndex_eq_negIndex_secondDiff, hpolar]
  obtain ⟨C, hC, hbound⟩ := quadratic_bound_of_posDef_secondDiff q hsecond
  refine ⟨C, hC, fun n => ?_⟩
  have he : q (Multiplicative.ofAdd (n : ℤ)) = conjChar χ (g ^ n) * k (g ^ n) := by
    change l (g ^ (n : ℤ)) = _
    rw [zpow_natCast]
  have hn : ‖conjChar χ (g ^ n)‖ = 1 := isUnitaryChar_conjChar hχ _
  simpa only [he, norm_mul, hn, one_mul] using hbound n

#print axioms cyclic_quadratic_of_positive_unitary_hyperplane

end GaloisForLFunctions.HeckeKreinToeplitz
