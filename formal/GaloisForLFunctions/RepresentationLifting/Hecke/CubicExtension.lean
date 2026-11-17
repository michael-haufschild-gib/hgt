import GaloisForLFunctions.RepresentationLifting.Hecke.PermutationKernel

/-!
# The cubic Hecke extension

An explicit basis displays the trivial-by-sign extension and proves that it does not split at the cubic exceptional parameters.
-/

noncomputable section
open Matrix
namespace GaloisForLFunctions.RepresentationLifting.Hecke

/-- Coordinates along the constant vector and the second coordinate vector. -/
def cubicKernelCoordinates : (ℂ × ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun z := ![z.1, z.1 + z.2]
  invFun v := (v 0, v 1 - v 0)
  left_inv z := by ext <;> simp
  right_inv v := by funext i; fin_cases i <;> simp
  map_add' z w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c z := by ext i; fin_cases i <;> simp <;> ring

/-- At the cubic divisor the two generators form a nontrivial extension of sign by trivial. -/
theorem cubic_kernel_triangular (t : ℂ) :
    (∀ z : ℂ × ℂ,
      kernelLeft t *ᵥ cubicKernelCoordinates z = cubicKernelCoordinates (t * z.1 + z.2, -z.2) ∧
      kernelRight t *ᵥ cubicKernelCoordinates z = cubicKernelCoordinates (t * z.1, -z.2)) ↔
      t ^ 2 + t + 1 = 0 := by
  constructor
  · intro h
    have hh := congrFun (h (1, 0)).2 1
    simp [kernelRight, cubicKernelCoordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hh
    linear_combination -hh
  · intro ht z
    constructor
    · ext i
      fin_cases i <;> simp [kernelLeft, cubicKernelCoordinates, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> ring
    · ext i
      fin_cases i
      · simp [kernelRight, cubicKernelCoordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · simp [kernelRight, cubicKernelCoordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        linear_combination -z.1 * ht

/-- No common trivial-character functional retracts the constant vector. -/
theorem kernel_no_trivial_retraction (t : ℂ) :
    ¬ ∃ f : (Fin 2 → ℂ) →ₗ[ℂ] ℂ,
      (∀ v, f (kernelLeft t *ᵥ v) = t * f v) ∧
      (∀ v, f (kernelRight t *ᵥ v) = t * f v) ∧ f ![1, 1] = 1 := by
  rintro ⟨f, hL, hR, hu⟩
  have hdiff : kernelLeft t *ᵥ ![0, 1] - kernelRight t *ᵥ ![0, 1] = ![1, 1] := by
    ext i
    fin_cases i <;> simp [kernelLeft, kernelRight]
  have hz : f ![1, 1] = 0 := by
    rw [← hdiff, map_sub, hL, hR, sub_self]
  exact zero_ne_one (hz.symm.trans hu)

/-- The sign quotient has exactly the trivial line as kernel. -/
def cubicSignQuotient : (Fin 2 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := v 0 - v 1
  map_add' _ _ := by simp only [Pi.add_apply]; ring
  map_smul' _ _ := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem cubicSignQuotient_kernel (v : Fin 2 → ℂ) :
    cubicSignQuotient v = 0 ↔ ∃ c : ℂ, v = c • ![1, 1] := by
  change v 0 - v 1 = 0 ↔ _
  constructor
  · intro hv
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i
    · simp
    · simpa using (sub_eq_zero.mp hv).symm
  · rintro ⟨c, rfl⟩
    simp

/-- The quotient is the sign character precisely at the cubic exceptional parameters. -/
theorem cubicSignQuotient_intertwines_iff (t : ℂ) :
    ((∀ v, cubicSignQuotient (kernelLeft t *ᵥ v) = -cubicSignQuotient v) ∧
      ∀ v, cubicSignQuotient (kernelRight t *ᵥ v) = -cubicSignQuotient v) ↔
      t ^ 2 + t + 1 = 0 := by
  constructor
  · intro h
    have hh := h.2 ![1, 0]
    simp [cubicSignQuotient, kernelRight] at hh
    linear_combination hh
  · intro ht
    constructor
    · intro v
      simp [cubicSignQuotient, kernelLeft, dotProduct, Fin.sum_univ_two]
      ring
    · intro v
      simp [cubicSignQuotient, kernelRight, dotProduct, Fin.sum_univ_two]
      linear_combination v 0 * ht

#print axioms cubic_kernel_triangular
#print axioms kernel_no_trivial_retraction
#print axioms cubicSignQuotient_intertwines_iff
#print axioms cubicSignQuotient_kernel
end GaloisForLFunctions.RepresentationLifting.Hecke
