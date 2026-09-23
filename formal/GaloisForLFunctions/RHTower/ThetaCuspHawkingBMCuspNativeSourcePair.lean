import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspCutoffMean
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspFieldIntegral

/-!
# Exact source projection in the original modular Hilbert pairing with every actual cusp test.

This leaf proves the displayed source or cusp identity. Causal continuation,
left-QNM evaluation and Hawking-clock extinction remain separate obligations.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate
namespace RHTower.D4BMCuspProjection
open D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

/-- The exact native pairing of the full admitted forcing with every actual
cusp test is its derived horizontal mean with the original hyperbolic density. -/
theorem forcingVector_cusp_inner (q : XiZeroCopy) (branch : Bool) (h : CuspHeightTest) :
    inner ℂ (h.operatorVector : Space) (forcingVector q branch) =
      ∫ y in Ioi 2, conj (h.field y)*mean (fun x => forcing q branch ![x,y])/(y:ℂ)^(2 : ℕ) := by
  have he : (fun z : UpperHalfPlane =>
      inner ℂ ((h.operatorVector : Space) z) (forcingVector q branch z)) =ᵐ[measure]
      (fun z => conj (h.field z.im)*forcing q branch ![z.re,z.im]) := by
    filter_upwards [h.operatorVector_coe,forcingVector_coe q branch] with z hh hf
    rw [hh,hf]
    simp [RCLike.inner_apply,coordinates,mul_comm]
  have hi := (L2.integrable_inner (𝕜 := ℂ) (h.operatorVector : Space)
    (forcingVector q branch)).congr he
  rw [L2.inner_def,integral_congr_ae he]
  change (∫ z : UpperHalfPlane, conj (h.field (z:ℂ).im)*forcing q branch ![(z:ℂ).re,(z:ℂ).im] ∂measure)=_
  rw [integral_cusp_field_from 2 (by norm_num) (fun z => conj (h.field z.im)*forcing q branch ![z.re,z.im]) hi
    (fun z hz => by rw [h.zero_low hz]; simp)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  congr 1
  change mean (fun x => conj (h.field y)*forcing q branch ![x,y]) = _
  exact integral_const_mul _ _

/-- Native source pairing with the complete explicit cusp projection, including
all cutoff derivatives and every opposite Fourier pair. -/
theorem forcingVector_cusp_inner_explicit (q : XiZeroCopy) (branch : Bool) (h : CuspHeightTest) :
    inner ℂ (h.operatorVector : Space) (forcingVector q branch) =
      ∫ y in Ioi 2, conj (h.field y)*
        ((parameter q branch/2)*(principal (center q) ![0,y] ^(2 : ℕ)+
          8*∑' N, amplitude (center q) y N^(2 : ℕ))-
          ((y:ℂ)^(2 : ℕ)*deriv (deriv (cutoffHeight q branch)) y-
            parameter q branch*cutoffHeight q branch y))/(y:ℂ)^(2 : ℕ) := by
  rw [forcingVector_cusp_inner]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [mean_forcing q branch (y := y) (by change 2 < y at hy; linarith)]

end
end RHTower.D4BMCuspProjection
