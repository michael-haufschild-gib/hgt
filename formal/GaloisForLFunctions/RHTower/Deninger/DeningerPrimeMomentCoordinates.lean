import GaloisForLFunctions.RHTower.Deninger.DeningerRationalDivisorSequence
import GaloisForLFunctions.HTGeometry.GroupAlgebras.FirstJet
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicScalingAction

/-!
# Prime coordinates for complex rational-scaling moments

The rational divisor map has a section given by products of prime powers.
Reconstruction recovers a nonzero rational up to sign, so twice its additive
class is recovered exactly. After extension of scalars to `ℂ`, multiplication
by two is injective and the divisor map becomes a linear equivalence.

Thus the complex first-moment space of rational scaling labels is exactly
the space of finitely supported complex families indexed by primes.
-/

open scoped TensorProduct
noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower

private theorem divisor_injective_positive {u v : ℚˣ} (hu : 0 < (u : ℚ))
    (hv : 0 < (v : ℚ)) (h : deningerDivisor u = deningerDivisor v) : u = v := by
  have hpos : 0 < ((u / v : ℚˣ) : ℚ) := by simpa using div_pos hu hv
  have hz : deningerDivisor (u / v) = 0 := by
    have hm := deningerDivisor_mul (u / v) v
    rw [div_mul_cancel] at hm
    rw [h] at hm
    exact add_right_cancel (hm.symm.trans (zero_add _).symm)
  exact div_eq_one.mp ((deningerDivisor_eq_zero_iff hpos).mp hz)

/-- The additive prime divisor map on the actual rational-scaling group. -/
def divisorLinear : Additive CCMRationalAdelicScaling →ₗ[ℤ] (Nat.Primes →₀ ℤ) :=
  AddMonoidHom.toIntLinearMap {
    toFun g := deningerDivisor g.toMul.val
    map_zero' := (deningerDivisor_eq_zero_iff (by norm_num : (0 : ℚ) < 1)).mpr rfl
    map_add' g h := deningerDivisor_mul g.toMul.val h.toMul.val }

/-- A section of the divisor map, realized by positive products of prime powers. -/
def divisorProductLinear : (Nat.Primes →₀ ℤ) →ₗ[ℤ] Additive CCMRationalAdelicScaling :=
  AddMonoidHom.toIntLinearMap {
    toFun n := Additive.ofMul ⟨deningerDivisorProduct n⟩
    map_zero' := by
      change Additive.ofMul (⟨deningerDivisorProduct 0⟩ : CCMRationalAdelicScaling) = 0
      have h : deningerDivisorProduct 0 = 1 :=
        (deningerDivisor_eq_zero_iff (deningerDivisorProduct_pos 0)).mp
          (deningerDivisor_divisorProduct 0)
      rw [h]; rfl
    map_add' n m := by
      apply congrArg Additive.ofMul
      apply ccmRationalAdelicScalingEquiv.injective
      change deningerDivisorProduct (n + m) = deningerDivisorProduct n * deningerDivisorProduct m
      apply divisor_injective_positive (deningerDivisorProduct_pos (n + m))
        (mul_pos (deningerDivisorProduct_pos n) (deningerDivisorProduct_pos m))
      rw [deningerDivisor_mul, deningerDivisor_divisorProduct,
        deningerDivisor_divisorProduct, deningerDivisor_divisorProduct] }

theorem divisor_right_inverse (n : Nat.Primes →₀ ℤ) :
    divisorLinear (divisorProductLinear n) = n := deningerDivisor_divisorProduct n

/-- Squaring removes the only ambiguity left by prime valuations. -/
theorem divisor_double_reconstruction (g : Additive CCMRationalAdelicScaling) :
    (2 : ℤ) • divisorProductLinear (divisorLinear g) = (2 : ℤ) • g := by
  apply congrArg Additive.ofMul
  change (⟨deningerDivisorProduct (deningerDivisor g.toMul.val)⟩ : CCMRationalAdelicScaling)^2 = g.toMul^2
  apply ccmRationalAdelicScalingEquiv.injective
  change deningerDivisorProduct (deningerDivisor g.toMul.val)^2 = g.toMul.val^2
  apply divisor_injective_positive
    (pow_pos (deningerDivisorProduct_pos _) 2)
    (sq_pos_iff.mpr (Units.ne_zero _))
  simp only [pow_two, deningerDivisor_mul, deningerDivisor_divisorProduct]

/-- The divisor map after complex scalar extension. -/
def divisorTensor : (ℂ ⊗[ℤ] Additive CCMRationalAdelicScaling) →ₗ[ℂ]
    ℂ ⊗[ℤ] (Nat.Primes →₀ ℤ) :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℂ →ₗ[ℂ] ℂ) divisorLinear

/-- The complex-linear extension of the positive prime-product section. -/
def divisorProductTensor : (ℂ ⊗[ℤ] (Nat.Primes →₀ ℤ)) →ₗ[ℂ]
    ℂ ⊗[ℤ] Additive CCMRationalAdelicScaling :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℂ →ₗ[ℂ] ℂ) divisorProductLinear

theorem divisorTensor_right_inverse (x : ℂ ⊗[ℤ] (Nat.Primes →₀ ℤ)) :
    divisorTensor (divisorProductTensor x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r n =>
    change r ⊗ₜ[ℤ] divisorLinear (divisorProductLinear n) = r ⊗ₜ[ℤ] n
    rw [divisor_right_inverse]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem divisorTensor_left_inverse (x : ℂ ⊗[ℤ] Additive CCMRationalAdelicScaling) :
    divisorProductTensor (divisorTensor x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r g =>
    change r ⊗ₜ[ℤ] divisorProductLinear (divisorLinear g) = r ⊗ₜ[ℤ] g
    have h := congrArg (fun a => r ⊗ₜ[ℤ] a) (divisor_double_reconstruction g)
    simp only [TensorProduct.tmul_smul] at h
    have h' : (2 : ℂ) • (r ⊗ₜ[ℤ] divisorProductLinear (divisorLinear g)) =
        (2 : ℂ) • (r ⊗ₜ[ℤ] g) := by simpa only [two_smul] using h
    exact (smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0)) h'
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Complex scalar extension removes exactly the finite sign ambiguity. -/
def divisorTensorEquiv : (ℂ ⊗[ℤ] Additive CCMRationalAdelicScaling) ≃ₗ[ℂ]
    ℂ ⊗[ℤ] (Nat.Primes →₀ ℤ) :=
  LinearEquiv.ofLinear divisorTensor divisorProductTensor
    (LinearMap.ext divisorTensor_right_inverse) (LinearMap.ext divisorTensor_left_inverse)

/-- Complex rational-scaling moments have exactly one coordinate per prime. -/
def deningerPrimeMomentEquiv : (ℂ ⊗[ℤ] Additive CCMRationalAdelicScaling) ≃ₗ[ℂ]
    (Nat.Primes →₀ ℂ) :=
  divisorTensorEquiv.trans (TensorProduct.finsuppScalarRight ℤ ℂ ℂ Nat.Primes)

#print axioms divisor_double_reconstruction
#print axioms deningerPrimeMomentEquiv
end RHTower
