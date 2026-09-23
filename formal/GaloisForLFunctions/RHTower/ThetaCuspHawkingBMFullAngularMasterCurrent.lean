import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCovector

/-!
The constructed covector cancels the resolvent defect in the original two-factor mixed master current. This is an angular and exterior-current identity; physical horizon, boundary, gauge and left-pairing admission remain separate obligations.
-/

open UpperHalfPlane
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMHorizon D4BMQuadraticMixedSource
noncomputable section

/-- The original fundamental time rate, with its physical damping shift. -/
def physicalRate (q : XiZeroCopy) (branch : Bool) : ℂ :=
  if branch then (q.1 : ℂ)-2 else -(q.1 : ℂ)-1

/-- The constructed inverse uses exactly the doubled-rate parameter of the mixed current. -/
theorem parameter_physicalRate (q : XiZeroCopy) (branch : Bool) :
    parameter q branch = resolventParameter (physicalRate q branch) := by
  cases branch <;> rfl

/-- The actual squared-source covector is precisely the retained Einstein-source pair. -/
theorem fullSquareCovector_source (q : XiZeroCopy) (z : Fin 2 → ℝ) :
    (fullSquareCovector q 0 z,fullSquareCovector q 1 z) =
      squareCovector (scalar (center q) z) (coordDeriv 0 (scalar (center q)) z)
        (coordDeriv 1 (scalar (center q)) z) := by
  simp only [fullSquareCovector,coexact,Matrix.cons_val_zero,Matrix.cons_val_one,
    squareCovector,mul_neg,neg_mul]

/-- The actual gradient-source component, retaining both first and second scalar derivatives. -/
def fullGradientCovector (q : XiZeroCopy) (branch : Bool) (k : Fin 2) (z : Fin 2 → ℝ) : ℂ :=
  let S := scalar (center q)
  let K := gradientCovector (physicalRate q branch) (z 1) (S z)
    (coordDeriv 0 S z) (coordDeriv 1 S z) (coordDeriv 0 (coordDeriv 0 S) z)
    (coordDeriv 0 (coordDeriv 1 S) z)
  if k = 0 then K.1 else K.2

/-- The two complete radial master factors minus the original mixed current. -/
def mixedMasterResidual (s r B J K A D : ℂ) : ℂ :=
  D4BMVectorStream.master (2*s) r (B^(2 : ℕ)) (B^(2 : ℕ)*(2*s)/(r*(r^(2 : ℕ)-1)))
    (B^(2 : ℕ)*((2*s)^(2 : ℕ)-(2*s)*(3*r^(2 : ℕ)-1))/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ))) A D -
  (s*(s-1)/4)*D4BMVectorStream.master (2*s) r (B^(2 : ℕ)/r^(2 : ℕ))
    (B^(2 : ℕ)*(-2/r^(3 : ℕ)+(2*s)/(r^(3 : ℕ)*(r^(2 : ℕ)-1))))
    (B^(2 : ℕ)*(6/r^(4 : ℕ)-4*(2*s)/(r^(4 : ℕ)*(r^(2 : ℕ)-1))+
      ((2*s)^(2 : ℕ)-(2*s)*(3*r^(2 : ℕ)-1))/(r^(4 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)))) J
    (2*(s+1)*(s+2)*J+2*K) - 2*current s r B J K

/-- The constructed covector cancels the actual mixed-current resolvent defect at every
angular point and exterior radius. Its actual rough Laplacian retains the curvature shift. -/
theorem fullAngular_master_current (q : XiZeroCopy) (branch : Bool)
    (z : UpperHalfPlane) (r : {r : ℝ // 1 < r}) (B : ℂ) (k : Fin 2) :
    mixedMasterResidual (physicalRate q branch) (r.1 : ℂ) B
      (fullSquareCovector q k (coordinates z))
      (fullGradientCovector q branch k (coordinates z))
      (fullAngularCovector q branch k (coordinates z))
      (roughLaplacian (fullAngularCovector q branch) k (coordinates z) +
        fullAngularCovector q branch k (coordinates z)) = 0 := by
  have hr : (r.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [r.2])
  have hf : (r.1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : r.1^(2 : ℕ)-1 ≠ 0 := by nlinarith [r.2]
    exact_mod_cast h
  rw [mixedMasterResidual,master_resolvent_defect _ _ _ _ _ _ _ hr hf,
    fullAngularCovector_rough_equation q branch (coordinates z) z.im_pos k,
    parameter_physicalRate]
  dsimp only [resolventParameter]
  ring

end
end RHTower.D4BMModularCore
