import GaloisForLFunctions.HeckeKreinToeplitz.Index.TorusFejerCorrections

/-!
# Exact Fourier coefficients of Toeplitz Fejér densities

Character orthogonality counts window pairs at each frequency. The zero
coefficient of an injective nonempty window is the kernel value at the identity.
-/

open Complex Finset Matrix MeasureTheory
open scoped ComplexConjugate Classical
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {I : Type*} [Countable I] {n : ℕ}

private theorem ofReal_hermQuad_eq {J : Type*} [Fintype J]
    {A : Matrix J J ℂ} (hA : A.IsHermitian) (v : J → ℂ) :
    (hermQuad A v : ℂ) = star v ⬝ᵥ A *ᵥ v := by
  apply Complex.ext
  · rfl
  · exact (hA.im_star_dotProduct_mulVec_self v).symm

/-- Each normalized Toeplitz density has the exact window-pair Fourier count. -/
theorem integral_torusKernelDensity_mul_character
    {k : Multiplicative (I →₀ ℤ) → ℂ} (hk : IsHermKernel k)
    (x : Fin n → I →₀ ℤ) (t : I →₀ ℤ) :
    (∫ θ, (torusKernelDensity k x θ : ℂ) * torusCharacter t θ ∂torusHaar I) =
      (∑ a, ∑ b, if x b - x a = t then k (Multiplicative.ofAdd t) else 0) / n := by
  classical
  have he (θ : UnitAddTorus I) :
      (torusKernelDensity k x θ : ℂ) * torusCharacter t θ =
        (∑ a, ∑ b, k (Multiplicative.ofAdd (x b - x a)) *
          torusCharacter (t - (x b - x a)) θ) / n := by
    unfold torusKernelDensity
    push_cast
    rw [ofReal_hermQuad_eq (gram_isHermitian hk _)]
    simp only [dotProduct, mulVec, Pi.star_apply, mul_sum]
    rw [div_mul_eq_mul_div]
    simp only [sum_mul]
    congr 1
    apply sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    have hindex : (Multiplicative.ofAdd (x a))⁻¹ * Multiplicative.ofAdd (x b) =
        Multiplicative.ofAdd (x b - x a) := by
      change Multiplicative.ofAdd (-x a + x b) = _
      congr 1
      abel
    rw [gram, hindex, Complex.star_def, ← torusCharacter_neg_index, neg_neg]
    rw [show t - (x b - x a) = x a + (-x b + t) by abel,
      torusCharacter_add_index, torusCharacter_add_index]
    ring
  have hint (a b : Fin n) : Integrable
      (fun θ => k (Multiplicative.ofAdd (x b - x a)) *
        torusCharacter (t - (x b - x a)) θ) (torusHaar I) :=
    ((torusCharacter (t - (x b - x a))).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  simp_rw [he]
  rw [integral_div, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
  simp_rw [integral_finsetSum _ fun b _ => hint _ b, integral_const_mul,
    integral_torusCharacter, sub_eq_zero]
  congr 1
  apply sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  by_cases hab : x b - x a = t
  · simp only [hab, if_true, mul_one]
  · rw [if_neg (Ne.symm hab), if_neg hab, mul_zero]

/-- Every nonempty injective window has the same signed density mass. -/
theorem integral_torusKernelDensity
    {k : Multiplicative (I →₀ ℤ) → ℂ} (hk : IsHermKernel k)
    (x : Fin n → I →₀ ℤ) (hx : Function.Injective x) (hn : 0 < n) :
    (∫ θ, torusKernelDensity k x θ ∂torusHaar I) = (k 1).re := by
  classical
  have h := integral_torusKernelDensity_mul_character hk x 0
  have hsum : (∑ a, ∑ b, if x b - x a = 0 then k (Multiplicative.ofAdd 0) else 0) =
      (n : ℂ) * k 1 := by
    have hinner (a : Fin n) :
        (∑ b, if x b - x a = 0 then k (Multiplicative.ofAdd 0) else 0) = k 1 := by
      rw [sum_eq_single a]
      · simp only [sub_self, ite_true]
        rfl
      · intro b _ hba
        exact if_neg (fun hzero => hba (hx (sub_eq_zero.mp hzero)))
      · simp
    simp_rw [hinner]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [torusCharacter_zero, mul_one] at h
  rw [hsum, integral_complex_ofReal] at h
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcancel : (n : ℂ) * k 1 / n = k 1 := by field_simp [hn0]
  rw [hcancel] at h
  exact congrArg Complex.re h

end GaloisForLFunctions.HeckeKreinToeplitz
