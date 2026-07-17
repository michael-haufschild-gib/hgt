import GaloisForLFunctions.HTGeometry.EllipticGammaCommensurableFactorization
import GaloisForLFunctions.HTGeometry.EllipticGammaProduct

/-!
# Commensurable factorization of the actual elliptic-gamma product

This identifies the additive product already used by the elliptic-gamma hierarchy with the
multiplicative product and transfers the unconditional residue-class factorization to it.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- Equality of two nome powers is exactly additive commensurability of the corresponding clock
periods modulo the integer lattice.  This converts the multiplicative hypothesis used by the
elliptic-gamma product into the additive parameters used in supersymmetric indices and partition
functions. -/
theorem ellipticNome_pow_eq_pow_iff_additivePeriodCongruence
    (σ τ : ℂ) (m n : ℕ) :
    ellipticNome σ ^ m = ellipticNome τ ^ n ↔
      ∃ k : ℤ, (m : ℂ) * σ = (n : ℂ) * τ + (k : ℂ) := by
  rw [ellipticNome, ellipticNome, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    Complex.exp_eq_exp_iff_exists_int]
  let C : ℂ := 2 * Real.pi * I
  have hC : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (mod_cast Real.pi_ne_zero)) I_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hfactor : C * ((m : ℂ) * σ - (n : ℂ) * τ - (k : ℂ)) = 0 := by
      dsimp [C]
      linear_combination hk
    have hzero : (m : ℂ) * σ - (n : ℂ) * τ - (k : ℂ) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hC
    linear_combination hzero
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    dsimp [C] at hC ⊢
    calc
      (m : ℂ) * (2 * Real.pi * I * σ) =
          (2 * Real.pi * I) * ((m : ℂ) * σ) := by ring
      _ = (2 * Real.pi * I) * ((n : ℂ) * τ + (k : ℂ)) := by rw [hk]
      _ = (n : ℂ) * (2 * Real.pi * I * τ) +
          (k : ℂ) * (2 * Real.pi * I) := by ring

/-- The existing additive elliptic-gamma product is the same actual product in its aligned
multiplicative coordinate. -/
theorem ellipticGammaProduct_eq_multiplicativeProduct (σ τ z : ℂ) :
    ellipticGammaProduct σ τ z =
      ellipticGammaMultiplicativeProduct (ellipticNome σ) (ellipticNome τ)
        (ellipticThetaCoordinate τ z) := by
  rfl

/-- Felder--Varchenko factorization for the actual additive elliptic-gamma product, stated in the
multiplicative coordinate in which commensurability is intrinsic. -/
theorem ellipticGammaProduct_commensurable_factorization
    {σ τ P z : ℂ} {m n : ℕ} [NeZero m] [NeZero n]
    (hp : ellipticNome σ ^ m = P) (hq : ellipticNome τ ^ n = P) :
    ellipticGammaProduct σ τ z =
      ellipticGammaCommensurableFamilyProduct
        (ellipticNome σ) (ellipticNome τ) P (ellipticThetaCoordinate τ z) m n := by
  rw [ellipticGammaProduct_eq_multiplicativeProduct]
  exact ellipticGammaMultiplicativeProduct_flattened_factorization
    (ellipticNome_ne_zero σ) (ellipticNome_ne_zero τ)
    (ellipticThetaCoordinate_ne_zero τ z) hp hq

/-- Additive-period form of the actual elliptic-gamma factorization.  One clock congruence
discharges both common-nome hypotheses and produces the common nome canonically as `p^m`. -/
theorem ellipticGammaProduct_additivePeriod_factorization
    {σ τ z : ℂ} {m n : ℕ} [NeZero m] [NeZero n]
    (hperiod : ∃ k : ℤ, (m : ℂ) * σ = (n : ℂ) * τ + (k : ℂ)) :
    ellipticGammaProduct σ τ z =
      ellipticGammaCommensurableFamilyProduct
        (ellipticNome σ) (ellipticNome τ) (ellipticNome σ ^ m)
        (ellipticThetaCoordinate τ z) m n := by
  apply ellipticGammaProduct_commensurable_factorization rfl
  exact (ellipticNome_pow_eq_pow_iff_additivePeriodCongruence σ τ m n).2 hperiod |>.symm

end

end GaloisForLFunctions
