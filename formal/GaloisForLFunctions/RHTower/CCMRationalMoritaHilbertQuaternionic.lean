import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import GaloisForLFunctions.RHTower.CCMRationalQuaternionicMoritaFiber

/-!
# Quaternionic antiunitary on the rational CCM Morita Hilbert fiber

This file realizes the sign-reflection from
`CCMRationalQuaternionicMoritaFiber` on the actual Hilbert space
`ℓ²(CCMRationalUnit, ℂ)`. It proves square `-1` and norm preservation, and packages the
operator as a conjugate-linear isometric equivalence without doubling the CCM fiber.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

abbrev CCMRationalMoritaHilbert :=
  lp (fun _ : CCMRationalUnit => ℂ) 2

theorem ccmRationalUnitSign_norm (q : CCMRationalUnit) :
    ‖ccmRationalUnitSign q‖ = 1 := by
  have hsq := congrArg norm (ccmRationalUnitSign_sq q)
  rw [norm_mul, norm_one] at hsq
  nlinarith [norm_nonneg (ccmRationalUnitSign q)]

def ccmRationalMoritaHilbertReflectionFunction
    (f : CCMRationalMoritaHilbert) (q : CCMRationalUnit) : ℂ :=
  ccmRationalUnitSign q * star (f (-q))

theorem ccmRationalMoritaHilbertReflectionFunction_memℓp
    (f : CCMRationalMoritaHilbert) :
    Memℓp (ccmRationalMoritaHilbertReflectionFunction f) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hf := (lp.memℓp f).summable (by norm_num)
  have hneg :
      Summable (fun q : CCMRationalUnit => ‖f (-q)‖ ^ (2 : ℕ)) := by
    have ht :=
      (Equiv.neg CCMRationalUnit).summable_iff.mpr (by simpa using hf)
    exact ht.congr (fun q => by
      dsimp only [Function.comp_apply]
      rw [Equiv.neg_apply])
  simpa [ccmRationalMoritaHilbertReflectionFunction,
    norm_mul, ccmRationalUnitSign_norm] using hneg

def ccmRationalMoritaHilbertReflection
    (f : CCMRationalMoritaHilbert) : CCMRationalMoritaHilbert :=
  ⟨ccmRationalMoritaHilbertReflectionFunction f,
    ccmRationalMoritaHilbertReflectionFunction_memℓp f⟩

@[simp]
theorem ccmRationalMoritaHilbertReflection_apply
    (f : CCMRationalMoritaHilbert) (q : CCMRationalUnit) :
    ccmRationalMoritaHilbertReflection f q =
      ccmRationalUnitSign q * star (f (-q)) :=
  rfl

theorem ccmRationalMoritaHilbertReflection_add
    (f g : CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertReflection (f + g) =
      ccmRationalMoritaHilbertReflection f +
        ccmRationalMoritaHilbertReflection g := by
  ext q
  change ccmRationalUnitSign q * star (f (-q) + g (-q)) =
    ccmRationalUnitSign q * star (f (-q)) +
      ccmRationalUnitSign q * star (g (-q))
  rw [star_add, mul_add]

theorem ccmRationalMoritaHilbertReflection_smul
    (z : ℂ) (f : CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertReflection (z • f) =
      star z • ccmRationalMoritaHilbertReflection f := by
  ext q
  simp [ccmRationalMoritaHilbertReflection_apply]
  ring

theorem ccmRationalMoritaHilbertReflection_sq
    (f : CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertReflection
      (ccmRationalMoritaHilbertReflection f) = -f := by
  ext q
  exact congrFun (ccmRationalQuaternionicReflection_sq
    (f : CCMRationalUnit → ℂ)) q

theorem ccmRationalMoritaHilbertReflection_norm
    (f : CCMRationalMoritaHilbert) :
    ‖ccmRationalMoritaHilbertReflection f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num),
    lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  rw [← (Equiv.neg CCMRationalUnit).tsum_eq]
  apply tsum_congr
  intro q
  simp [ccmRationalMoritaHilbertReflection_apply,
    ccmRationalUnitSign_norm]

theorem ccmRationalMoritaHilbertReflection_neg
    (f : CCMRationalMoritaHilbert) :
    ccmRationalMoritaHilbertReflection (-f) =
      -ccmRationalMoritaHilbertReflection f := by
  simpa using ccmRationalMoritaHilbertReflection_smul (-1 : ℂ) f

def ccmRationalMoritaHilbertQuaternionicIsometry :
    CCMRationalMoritaHilbert ≃ₗᵢ⋆[ℂ] CCMRationalMoritaHilbert where
  toFun := ccmRationalMoritaHilbertReflection
  invFun := fun f => -ccmRationalMoritaHilbertReflection f
  left_inv f := by
    change -ccmRationalMoritaHilbertReflection
      (ccmRationalMoritaHilbertReflection f) = f
    rw [ccmRationalMoritaHilbertReflection_sq]
    simp
  right_inv f := by
    change ccmRationalMoritaHilbertReflection
      (-ccmRationalMoritaHilbertReflection f) = f
    rw [ccmRationalMoritaHilbertReflection_neg,
      ccmRationalMoritaHilbertReflection_sq]
    simp
  map_add' := ccmRationalMoritaHilbertReflection_add
  map_smul' := ccmRationalMoritaHilbertReflection_smul
  norm_map' := ccmRationalMoritaHilbertReflection_norm

end RHTower
end GaloisForLFunctions
